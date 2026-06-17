import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.GammaBinetStirling.BinetAbelPlanaCore
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Cotangent
import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# Finite-strip cotangent remainder bounds

This file owns the cotangent-kernel estimates used to discard the horizontal
finite-height Abel-Plana contour edges.  The public API is intentionally only
about the cotangent kernel; logarithmic growth estimates and contour assembly
belong to the horizontal-bound files downstream.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped Topology
open Filter

namespace Complex

/-- Upper-half-plane cotangent exponential parameter on the finite horizontal
line `x + iT`. -/
noncomputable def finiteAbelPlanaCotangentUpperQ
    (x T : ℝ) : ℂ :=
  Complex.exp ((2 : ℂ) * (Real.pi : ℂ) * Complex.I *
    ((x : ℂ) + (T : ℂ) * Complex.I))

/-- Lower-half-plane cotangent exponential parameter on the finite horizontal
line `x - iT`, written with the reciprocal exponential so that it is small as
`T → +∞`. -/
noncomputable def finiteAbelPlanaCotangentLowerQ
    (x T : ℝ) : ℂ :=
  Complex.exp (-((2 : ℂ) * (Real.pi : ℂ) * Complex.I *
    ((x : ℂ) - (T : ℂ) * Complex.I)))

/-- Imaginary part of the upper finite-strip horizontal point. -/
theorem finiteAbelPlanaCotangentUpperPoint_im
    (x T : ℝ) :
    (((x : ℂ) + (T : ℂ) * Complex.I).im) = T := by
  calc
    (((x : ℂ) + (T : ℂ) * Complex.I).im) =
        (x : ℂ).im + ((T : ℂ) * Complex.I).im :=
      Complex.add_im (x : ℂ) ((T : ℂ) * Complex.I)
    _ = 0 + ((T : ℂ) * Complex.I).im := by
      exact congrArg
        (fun u : ℝ => u + ((T : ℂ) * Complex.I).im)
        (Complex.ofReal_im x)
    _ = 0 + (T : ℂ).re := by
      exact congrArg (fun u : ℝ => 0 + u) (Complex.mul_I_im (T : ℂ))
    _ = 0 + T := by
      exact congrArg (fun u : ℝ => 0 + u) (Complex.ofReal_re T)
    _ = T := zero_add T

/-- Imaginary part of the lower finite-strip horizontal point. -/
theorem finiteAbelPlanaCotangentLowerPoint_im
    (x T : ℝ) :
    (((x : ℂ) - (T : ℂ) * Complex.I).im) = -T := by
  calc
    (((x : ℂ) - (T : ℂ) * Complex.I).im) =
        (x : ℂ).im - ((T : ℂ) * Complex.I).im :=
      Complex.sub_im (x : ℂ) ((T : ℂ) * Complex.I)
    _ = 0 - ((T : ℂ) * Complex.I).im := by
      exact congrArg
        (fun u : ℝ => u - ((T : ℂ) * Complex.I).im)
        (Complex.ofReal_im x)
    _ = 0 - (T : ℂ).re := by
      exact congrArg (fun u : ℝ => 0 - u) (Complex.mul_I_im (T : ℂ))
    _ = 0 - T := by
      exact congrArg (fun u : ℝ => 0 - u) (Complex.ofReal_re T)
    _ = -T := zero_sub T

/-- Real part of multiplication by `(2π)i`: it is `-2π` times the imaginary
part of the right factor. -/
theorem finiteAbelPlanaCotangentTwoPiI_mul_re
    (z : ℂ) :
    (((2 : ℂ) * (Real.pi : ℂ) * Complex.I * z).re) =
      -((2 : ℝ) * Real.pi * z.im) := by
  let a : ℂ := (2 : ℂ) * (Real.pi : ℂ)
  have ha_re : a.re = (2 : ℝ) * Real.pi := by
    show (((2 : ℂ) * (Real.pi : ℂ)).re) = (2 : ℝ) * Real.pi
    calc
      (((2 : ℂ) * (Real.pi : ℂ)).re) =
          (2 : ℂ).re * (Real.pi : ℂ).re -
            (2 : ℂ).im * (Real.pi : ℂ).im :=
        Complex.mul_re (2 : ℂ) (Real.pi : ℂ)
      _ = (2 : ℝ) * Real.pi - 0 * (Real.pi : ℂ).im := by
        exact congrArg₂ Sub.sub
          (congrArg₂ HMul.hMul
            (Complex.ofReal_re (2 : ℝ))
            (Complex.ofReal_re Real.pi))
          (congrArg (fun u : ℝ => u * (Real.pi : ℂ).im)
            (Complex.ofReal_im (2 : ℝ)))
      _ = (2 : ℝ) * Real.pi - 0 * 0 := by
        exact congrArg
          (fun u : ℝ => (2 : ℝ) * Real.pi - 0 * u)
          (Complex.ofReal_im Real.pi)
      _ = (2 : ℝ) * Real.pi - 0 := by
        exact congrArg
          (fun u : ℝ => (2 : ℝ) * Real.pi - u)
          (zero_mul (0 : ℝ))
      _ = (2 : ℝ) * Real.pi := sub_zero ((2 : ℝ) * Real.pi)
  have ha_im : a.im = 0 := by
    show (((2 : ℂ) * (Real.pi : ℂ)).im) = 0
    calc
      (((2 : ℂ) * (Real.pi : ℂ)).im) =
          (2 : ℂ).re * (Real.pi : ℂ).im +
            (2 : ℂ).im * (Real.pi : ℂ).re :=
        Complex.mul_im (2 : ℂ) (Real.pi : ℂ)
      _ = (2 : ℂ).re * 0 + (2 : ℂ).im * (Real.pi : ℂ).re := by
        exact congrArg₂ HAdd.hAdd
          (congrArg (fun u : ℝ => (2 : ℂ).re * u)
            (Complex.ofReal_im Real.pi))
          rfl
      _ = (2 : ℂ).re * 0 + 0 * (Real.pi : ℂ).re := by
        exact congrArg
          (fun u : ℝ => (2 : ℂ).re * 0 + u * (Real.pi : ℂ).re)
          (Complex.ofReal_im (2 : ℝ))
      _ = 0 + 0 * (Real.pi : ℂ).re := by
        exact congrArg (fun u : ℝ => u + 0 * (Real.pi : ℂ).re)
          (mul_zero (2 : ℂ).re)
      _ = 0 + 0 := by
        exact congrArg (fun u : ℝ => 0 + u)
          (zero_mul (Real.pi : ℂ).re)
      _ = 0 := zero_add 0
  have hai_re : (a * Complex.I).re = 0 := by
    calc
      (a * Complex.I).re = -a.im := Complex.mul_I_re a
      _ = -0 := congrArg Neg.neg ha_im
      _ = 0 := neg_zero
  have hai_im : (a * Complex.I).im = (2 : ℝ) * Real.pi := by
    calc
      (a * Complex.I).im = a.re := Complex.mul_I_im a
      _ = (2 : ℝ) * Real.pi := ha_re
  calc
    (((2 : ℂ) * (Real.pi : ℂ) * Complex.I * z).re) =
        ((a * Complex.I) * z).re := by
      rfl
    _ = (a * Complex.I).re * z.re - (a * Complex.I).im * z.im :=
      Complex.mul_re (a * Complex.I) z
    _ = 0 * z.re - ((2 : ℝ) * Real.pi) * z.im := by
      exact congrArg₂ Sub.sub
        (congrArg (fun u : ℝ => u * z.re) hai_re)
        (congrArg (fun u : ℝ => u * z.im) hai_im)
    _ = 0 - ((2 : ℝ) * Real.pi) * z.im := by
      exact congrArg
        (fun u : ℝ => u - ((2 : ℝ) * Real.pi) * z.im)
        (zero_mul z.re)
    _ = -(((2 : ℝ) * Real.pi) * z.im) := zero_sub (((2 : ℝ) * Real.pi) * z.im)

/-- Real part of the upper finite-strip cotangent exponential exponent. -/
theorem finiteAbelPlanaCotangentUpperExponent_re
    (x T : ℝ) :
    (((2 : ℂ) * (Real.pi : ℂ) * Complex.I *
      ((x : ℂ) + (T : ℂ) * Complex.I)).re) =
      -(2 * Real.pi * T) := by
  calc
    (((2 : ℂ) * (Real.pi : ℂ) * Complex.I *
      ((x : ℂ) + (T : ℂ) * Complex.I)).re) =
        -((2 : ℝ) * Real.pi *
          (((x : ℂ) + (T : ℂ) * Complex.I).im)) :=
      Complex.finiteAbelPlanaCotangentTwoPiI_mul_re
        ((x : ℂ) + (T : ℂ) * Complex.I)
    _ = -((2 : ℝ) * Real.pi * T) := by
      exact congrArg
        (fun u : ℝ => -((2 : ℝ) * Real.pi * u))
        (Complex.finiteAbelPlanaCotangentUpperPoint_im x T)

/-- Real part of the lower finite-strip cotangent reciprocal exponent. -/
theorem finiteAbelPlanaCotangentLowerExponent_re
    (x T : ℝ) :
    ((-((2 : ℂ) * (Real.pi : ℂ) * Complex.I *
      ((x : ℂ) - (T : ℂ) * Complex.I))).re) =
      -(2 * Real.pi * T) := by
  have hraw :
      (((2 : ℂ) * (Real.pi : ℂ) * Complex.I *
        ((x : ℂ) - (T : ℂ) * Complex.I)).re) =
        (2 : ℝ) * Real.pi * T := by
    calc
      (((2 : ℂ) * (Real.pi : ℂ) * Complex.I *
        ((x : ℂ) - (T : ℂ) * Complex.I)).re) =
          -((2 : ℝ) * Real.pi *
            (((x : ℂ) - (T : ℂ) * Complex.I).im)) :=
        Complex.finiteAbelPlanaCotangentTwoPiI_mul_re
          ((x : ℂ) - (T : ℂ) * Complex.I)
      _ = -((2 : ℝ) * Real.pi * (-T)) := by
        exact congrArg
          (fun u : ℝ => -((2 : ℝ) * Real.pi * u))
          (Complex.finiteAbelPlanaCotangentLowerPoint_im x T)
      _ = (2 : ℝ) * Real.pi * T := by
        calc
          -((2 : ℝ) * Real.pi * (-T)) =
              -(-((2 : ℝ) * Real.pi * T)) := by
            exact congrArg Neg.neg (mul_neg ((2 : ℝ) * Real.pi) T)
          _ = (2 : ℝ) * Real.pi * T := neg_neg ((2 : ℝ) * Real.pi * T)
  calc
    ((-((2 : ℂ) * (Real.pi : ℂ) * Complex.I *
      ((x : ℂ) - (T : ℂ) * Complex.I))).re) =
        -(((2 : ℂ) * (Real.pi : ℂ) * Complex.I *
          ((x : ℂ) - (T : ℂ) * Complex.I)).re) :=
      Complex.neg_re _
    _ = -((2 : ℝ) * Real.pi * T) := congrArg Neg.neg hraw

/-- The positive vertical-axis point is the upper finite-strip point at
horizontal coordinate `0`. -/
theorem finiteAbelPlanaCotangentKernel_upper_vertical_arg
    (t : ℝ) :
    ((0 : ℂ) + (t : ℂ) * Complex.I) =
      (t : ℂ) * Complex.I := by
  exact zero_add ((t : ℂ) * Complex.I)

/-- The negative vertical-axis point is the lower finite-strip point at
horizontal coordinate `0`. -/
theorem finiteAbelPlanaCotangentKernel_lower_vertical_arg
    (t : ℝ) :
    ((0 : ℂ) - (t : ℂ) * Complex.I) =
      -((t : ℂ) * Complex.I) := by
  calc
    (0 : ℂ) - (t : ℂ) * Complex.I =
        (0 : ℂ) + -((t : ℂ) * Complex.I) := by
      exact sub_eq_add_neg (0 : ℂ) ((t : ℂ) * Complex.I)
    _ = -((t : ℂ) * Complex.I) := by
      exact zero_add (-((t : ℂ) * Complex.I))

/-- Exact norm of the scalar `2πi` appearing in the cotangent remainder. -/
theorem norm_two_pi_I_eq_two_pi :
    ‖((2 : ℂ) * (Real.pi : ℂ) * Complex.I)‖ =
      (2 : ℝ) * Real.pi := by
  calc
    ‖((2 : ℂ) * (Real.pi : ℂ) * Complex.I)‖ =
        ‖((2 : ℂ) * (Real.pi : ℂ))‖ * ‖Complex.I‖ :=
      norm_mul ((2 : ℂ) * (Real.pi : ℂ)) Complex.I
    _ = (‖(2 : ℂ)‖ * ‖(Real.pi : ℂ)‖) * ‖Complex.I‖ := by
      exact congrArg (fun r : ℝ => r * ‖Complex.I‖)
        (norm_mul (2 : ℂ) (Real.pi : ℂ))
    _ = (2 * ‖(Real.pi : ℂ)‖) * ‖Complex.I‖ := by
      exact congrArg
        (fun r : ℝ => (r * ‖(Real.pi : ℂ)‖) * ‖Complex.I‖)
        (Complex.norm_ofNat 2)
    _ = (2 * ‖(Real.pi : ℂ)‖) * 1 := by
      exact congrArg (fun r : ℝ => (2 * ‖(Real.pi : ℂ)‖) * r)
        Complex.norm_I
    _ = 2 * ‖(Real.pi : ℂ)‖ := mul_one (2 * ‖(Real.pi : ℂ)‖)
    _ = 2 * |Real.pi| := by
      exact congrArg (fun r : ℝ => 2 * r)
        (RCLike.norm_ofReal Real.pi)
    _ = 2 * Real.pi := by
      exact congrArg (fun r : ℝ => 2 * r)
        (abs_of_nonneg Real.pi_pos.le)

/-- The scalar loss from the denominator estimate is absorbed by the displayed
`4(π+1)` horizontal constant. -/
theorem two_mul_norm_two_pi_I_le_four_pi_add_one :
    (2 : ℝ) * ‖((2 : ℂ) * (Real.pi : ℂ) * Complex.I)‖ ≤
      4 * (Real.pi + 1) := by
  have hnorm :
      (2 : ℝ) * ‖((2 : ℂ) * (Real.pi : ℂ) * Complex.I)‖ =
        4 * Real.pi := by
    calc
      (2 : ℝ) * ‖((2 : ℂ) * (Real.pi : ℂ) * Complex.I)‖ =
          2 * (2 * Real.pi) := by
        exact congrArg (fun r : ℝ => 2 * r) norm_two_pi_I_eq_two_pi
      _ = (2 * 2) * Real.pi := (mul_assoc (2 : ℝ) 2 Real.pi).symm
      _ = (2 + 2) * Real.pi := by
        exact congrArg (fun r : ℝ => r * Real.pi) (two_mul (2 : ℝ))
      _ = 4 * Real.pi := by
        have htwo_add_two : (2 : ℝ) + 2 = 4 := by
          calc
            (2 : ℝ) + 2 = ((2 + 2 : ℕ) : ℝ) := by
              exact (Nat.cast_add 2 2).symm
            _ = 4 := rfl
        exact congrArg
          (fun r : ℝ => r * Real.pi)
          htwo_add_two
  have hpi_le : 4 * Real.pi ≤ 4 * (Real.pi + 1) := by
    have hbase : Real.pi ≤ Real.pi + 1 := by
      exact le_add_of_nonneg_right zero_le_one
    exact mul_le_mul_of_nonneg_left hbase (show (0 : ℝ) ≤ 4 from zero_le_four)
  exact Eq.subst (motive := fun r : ℝ => r ≤ 4 * (Real.pi + 1)) hnorm.symm hpi_le

/-- Norm of the upper-half-plane cotangent exponential parameter. -/
theorem norm_finiteAbelPlanaCotangentUpperQ
    (x T : ℝ) :
    ‖Complex.finiteAbelPlanaCotangentUpperQ x T‖ =
      Real.exp (-(2 * Real.pi * T)) := by
  calc
    ‖Complex.finiteAbelPlanaCotangentUpperQ x T‖ =
        Complex.abs
          (Complex.exp ((2 : ℂ) * (Real.pi : ℂ) * Complex.I *
            ((x : ℂ) + (T : ℂ) * Complex.I))) := by
      exact Complex.norm_eq_abs _
    _ = Real.exp
        (((2 : ℂ) * (Real.pi : ℂ) * Complex.I *
          ((x : ℂ) + (T : ℂ) * Complex.I)).re) :=
      Complex.abs_exp _
    _ = Real.exp (-(2 * Real.pi * T)) := by
      exact congrArg Real.exp
        (Complex.finiteAbelPlanaCotangentUpperExponent_re x T)

/-- Norm of the lower-half-plane cotangent reciprocal-exponential parameter. -/
theorem norm_finiteAbelPlanaCotangentLowerQ
    (x T : ℝ) :
    ‖Complex.finiteAbelPlanaCotangentLowerQ x T‖ =
      Real.exp (-(2 * Real.pi * T)) := by
  calc
    ‖Complex.finiteAbelPlanaCotangentLowerQ x T‖ =
        Complex.abs
          (Complex.exp (-((2 : ℂ) * (Real.pi : ℂ) * Complex.I *
            ((x : ℂ) - (T : ℂ) * Complex.I)))) := by
      exact Complex.norm_eq_abs _
    _ = Real.exp
        ((-((2 : ℂ) * (Real.pi : ℂ) * Complex.I *
          ((x : ℂ) - (T : ℂ) * Complex.I))).re) :=
      Complex.abs_exp _
    _ = Real.exp (-(2 * Real.pi * T)) := by
      exact congrArg Real.exp
        (Complex.finiteAbelPlanaCotangentLowerExponent_re x T)

/-- The upper exponential cotangent parameter lies inside the unit disk for
positive height. -/
theorem norm_finiteAbelPlanaCotangentUpperQ_lt_one
    (x T : ℝ)
    (hT : 0 < T) :
    ‖Complex.finiteAbelPlanaCotangentUpperQ x T‖ < 1 := by
  have hnorm :
      ‖Complex.finiteAbelPlanaCotangentUpperQ x T‖ =
        Real.exp (-(2 * Real.pi * T)) :=
    Complex.norm_finiteAbelPlanaCotangentUpperQ x T
  have hneg : -(2 * Real.pi * T) < 0 := by
    have hpos : 0 < 2 * Real.pi * T :=
      mul_pos (mul_pos two_pos Real.pi_pos) hT
    exact neg_neg_of_pos hpos
  have hexp_lt : Real.exp (-(2 * Real.pi * T)) < 1 := by
    calc
      Real.exp (-(2 * Real.pi * T)) < Real.exp 0 :=
      Real.exp_lt_exp.mpr hneg
      _ = 1 := Real.exp_zero
  exact
    Eq.subst
      (motive := fun y : ℝ => y < 1)
      hnorm.symm
      hexp_lt

/-- The lower reciprocal-exponential cotangent parameter lies inside the unit
disk for positive height. -/
theorem norm_finiteAbelPlanaCotangentLowerQ_lt_one
    (x T : ℝ)
    (hT : 0 < T) :
    ‖Complex.finiteAbelPlanaCotangentLowerQ x T‖ < 1 := by
  have hnorm :
      ‖Complex.finiteAbelPlanaCotangentLowerQ x T‖ =
        Real.exp (-(2 * Real.pi * T)) :=
    Complex.norm_finiteAbelPlanaCotangentLowerQ x T
  have hneg : -(2 * Real.pi * T) < 0 := by
    have hpos : 0 < 2 * Real.pi * T :=
      mul_pos (mul_pos two_pos Real.pi_pos) hT
    exact neg_neg_of_pos hpos
  have hexp_lt : Real.exp (-(2 * Real.pi * T)) < 1 := by
    calc
      Real.exp (-(2 * Real.pi * T)) < Real.exp 0 :=
      Real.exp_lt_exp.mpr hneg
      _ = 1 := Real.exp_zero
  exact
    Eq.subst
      (motive := fun y : ℝ => y < 1)
      hnorm.symm
      hexp_lt

/-- The upper cotangent denominator is nonzero for positive height. -/
theorem finiteAbelPlanaCotangentUpperQ_ne_one
    (x T : ℝ)
    (hT : 0 < T) :
    Complex.finiteAbelPlanaCotangentUpperQ x T ≠ 1 := by
  intro hq
  have hnorm_lt :
      ‖Complex.finiteAbelPlanaCotangentUpperQ x T‖ < 1 :=
    Complex.norm_finiteAbelPlanaCotangentUpperQ_lt_one x T hT
  have hnorm_eq : ‖Complex.finiteAbelPlanaCotangentUpperQ x T‖ = 1 := by
    calc
      ‖Complex.finiteAbelPlanaCotangentUpperQ x T‖ = ‖(1 : ℂ)‖ := by
        exact congrArg norm hq
      _ = 1 := norm_one
  exact (lt_irrefl (1 : ℝ)) (hnorm_eq ▸ hnorm_lt)

/-- The lower cotangent denominator is nonzero for positive height. -/
theorem finiteAbelPlanaCotangentLowerQ_ne_one
    (x T : ℝ)
    (hT : 0 < T) :
    Complex.finiteAbelPlanaCotangentLowerQ x T ≠ 1 := by
  intro hq
  have hnorm_lt :
      ‖Complex.finiteAbelPlanaCotangentLowerQ x T‖ < 1 :=
    Complex.norm_finiteAbelPlanaCotangentLowerQ_lt_one x T hT
  have hnorm_eq : ‖Complex.finiteAbelPlanaCotangentLowerQ x T‖ = 1 := by
    calc
      ‖Complex.finiteAbelPlanaCotangentLowerQ x T‖ = ‖(1 : ℂ)‖ := by
        exact congrArg norm hq
      _ = 1 := norm_one
  exact (lt_irrefl (1 : ℝ)) (hnorm_eq ▸ hnorm_lt)

/-- Cancels the small cotangent denominator before the `I` division is
rewritten. -/
theorem cotangent_exp_ratio_cancel_denominator
    (q : ℂ)
    (hq : q ≠ 1) :
    ((q + 1) / (Complex.I * (1 - q))) * (1 - q) =
      (q + 1) / Complex.I := by
  have hden : (1 : ℂ) - q ≠ 0 := by
    intro hzero
    have hone_eq_q : (1 : ℂ) = q := sub_eq_zero.mp hzero
    exact hq hone_eq_q.symm
  have hIden : Complex.I * ((1 : ℂ) - q) ≠ 0 :=
    mul_ne_zero Complex.I_ne_zero hden
  apply (eq_div_iff_mul_eq Complex.I_ne_zero).mpr
  calc
    (((q + 1) / (Complex.I * (1 - q))) * (1 - q)) * Complex.I =
        ((q + 1) / (Complex.I * (1 - q))) * ((1 - q) * Complex.I) :=
      mul_assoc ((q + 1) / (Complex.I * (1 - q))) (1 - q) Complex.I
    _ =
        ((q + 1) / (Complex.I * (1 - q))) * (Complex.I * (1 - q)) := by
      exact congrArg
        (fun z : ℂ => ((q + 1) / (Complex.I * (1 - q))) * z)
        (mul_comm (1 - q) Complex.I)
    _ = q + 1 := by
      calc
        ((q + 1) / (Complex.I * (1 - q))) * (Complex.I * (1 - q)) =
            (Complex.I * (1 - q)) *
              ((q + 1) / (Complex.I * (1 - q))) := by
          exact mul_comm
            ((q + 1) / (Complex.I * (1 - q)))
            (Complex.I * (1 - q))
        _ = q + 1 := by
          exact mul_div_cancel₀ (q + 1) hIden

/-- Linear numerator cancellation for the upper cotangent remainder after
denominators have been cleared. -/
theorem cotangent_upper_linear_numerator_identity
    (q : ℂ) :
    (Real.pi : ℂ) * (-((q + 1) * Complex.I)) +
        ((Real.pi : ℂ) * Complex.I) * (1 - q) =
      -((2 : ℂ) * (Real.pi : ℂ) * Complex.I) * q := by
  let P : ℂ := (Real.pi : ℂ)
  let I : ℂ := Complex.I
  calc
    (Real.pi : ℂ) * (-((q + 1) * Complex.I)) +
        ((Real.pi : ℂ) * Complex.I) * (1 - q) =
        P * (-((q + 1) * I)) + (P * I) * (1 - q) := rfl
    _ = -(P * ((q + 1) * I)) + (P * I) * (1 - q) := by
      exact congrArg
        (fun z : ℂ => z + (P * I) * (1 - q))
        (mul_neg P ((q + 1) * I))
    _ = -((P * (q + 1)) * I) + (P * I) * (1 - q) := by
      exact congrArg
        (fun z : ℂ => -z + (P * I) * (1 - q))
        (mul_assoc P (q + 1) I).symm
    _ = -(((P * q) + (P * 1)) * I) + (P * I) * (1 - q) := by
      exact congrArg
        (fun z : ℂ => -(z * I) + (P * I) * (1 - q))
        (left_distrib P q 1)
    _ = -(((P * q) + P) * I) + (P * I) * (1 - q) := by
      exact congrArg
        (fun z : ℂ => -(((P * q) + z) * I) + (P * I) * (1 - q))
        (mul_one P)
    _ = -((P * q) * I + P * I) + (P * I) * (1 - q) := by
      exact congrArg
        (fun z : ℂ => -z + (P * I) * (1 - q))
        (right_distrib (P * q) P I)
    _ = -((P * q) * I) + -(P * I) + (P * I) * (1 - q) := by
      exact congrArg
        (fun z : ℂ => z + (P * I) * (1 - q))
        (neg_add ((P * q) * I) (P * I))
    _ = -((P * q) * I) + -(P * I) + ((P * I) * 1 + (P * I) * (-q)) := by
      exact congrArg
        (fun z : ℂ => -((P * q) * I) + -(P * I) + z)
        (left_distrib (P * I) 1 (-q))
    _ = -((P * q) * I) + -(P * I) + ((P * I) + (P * I) * (-q)) := by
      exact congrArg
        (fun z : ℂ => -((P * q) * I) + -(P * I) +
          (z + (P * I) * (-q)))
        (mul_one (P * I))
    _ = -((P * q) * I) + (-(P * I) + ((P * I) + (P * I) * (-q))) := by
      exact add_assoc (-((P * q) * I)) (-(P * I))
        ((P * I) + (P * I) * (-q))
    _ = -((P * q) * I) + ((-(P * I) + (P * I)) + (P * I) * (-q)) := by
      exact congrArg
        (fun z : ℂ => -((P * q) * I) + z)
        (add_assoc (-(P * I)) (P * I) ((P * I) * (-q))).symm
    _ = -((P * q) * I) + (0 + (P * I) * (-q)) := by
      exact congrArg
        (fun z : ℂ => -((P * q) * I) + (z + (P * I) * (-q)))
        (neg_add_cancel (P * I))
    _ = -((P * q) * I) + 0 + (P * I) * (-q) := by
      exact (add_assoc (-((P * q) * I)) 0 ((P * I) * (-q))).symm
    _ = -((P * q) * I) + (P * I) * (-q) := by
      exact zero_add ((P * I) * (-q)) ▸
        (add_zero (-((P * q) * I))).symm ▸ rfl
    _ = -((P * q) * I) + -((P * I) * q) := by
      exact congrArg
        (fun z : ℂ => -((P * q) * I) + z)
        (mul_neg (P * I) q)
    _ = -((P * q) * I) + -((P * I) * q) := rfl
    _ = -((P * (q * I))) + -((P * (I * q))) := by
      exact congrArg₂ HAdd.hAdd
        (congrArg Neg.neg (mul_assoc P q I))
        (congrArg Neg.neg (mul_assoc P I q))
    _ = -((P * (I * q))) + -((P * (I * q))) := by
      exact congrArg
        (fun z : ℂ => -(P * z) + -(P * (I * q)))
        (mul_comm q I)
    _ = -((P * (I * q)) + (P * (I * q))) := by
      exact (neg_add' (P * (I * q)) (P * (I * q))).symm
    _ = -((2 : ℂ) * (P * (I * q))) := by
      exact congrArg Neg.neg (two_mul (P * (I * q))).symm
    _ = -(((2 : ℂ) * P) * (I * q)) := by
      exact congrArg Neg.neg (mul_assoc (2 : ℂ) P (I * q)).symm
    _ = -((2 : ℂ) * P * I * q) := by
      exact congrArg Neg.neg (mul_assoc ((2 : ℂ) * P) I q).symm
    _ = -((2 : ℂ) * P * I) * q := by
      exact (neg_mul ((2 : ℂ) * P * I) q).symm
    _ = -((2 : ℂ) * (Real.pi : ℂ) * Complex.I) * q := rfl

/-- The upper cotangent exponential ratio after clearing the geometric
denominator. -/
theorem cotangent_upper_exp_ratio_identity_div
    (q : ℂ)
    (hq : q ≠ 1) :
    (Real.pi : ℂ) * ((q + 1) / (Complex.I * (1 - q))) +
        (Real.pi : ℂ) * Complex.I =
      (-((2 : ℂ) * (Real.pi : ℂ) * Complex.I) * q) / (1 - q) := by
  have hden : (1 : ℂ) - q ≠ 0 := by
    intro hzero
    have hone_eq_q : (1 : ℂ) = q := sub_eq_zero.mp hzero
    exact hq hone_eq_q.symm
  apply (eq_div_iff_mul_eq hden).mpr
  calc
    ((Real.pi : ℂ) * ((q + 1) / (Complex.I * (1 - q))) +
        (Real.pi : ℂ) * Complex.I) * (1 - q) =
        (Real.pi : ℂ) * ((q + 1) / (Complex.I * (1 - q))) * (1 - q) +
          ((Real.pi : ℂ) * Complex.I) * (1 - q) := by
      exact right_distrib
        ((Real.pi : ℂ) * ((q + 1) / (Complex.I * (1 - q))))
        ((Real.pi : ℂ) * Complex.I)
        (1 - q)
    _ =
        (Real.pi : ℂ) * (((q + 1) / (Complex.I * (1 - q))) * (1 - q)) +
          ((Real.pi : ℂ) * Complex.I) * (1 - q) := by
      exact congrArg
        (fun z : ℂ => z + ((Real.pi : ℂ) * Complex.I) * (1 - q))
        (mul_assoc (Real.pi : ℂ)
          ((q + 1) / (Complex.I * (1 - q))) (1 - q))
    _ =
        (Real.pi : ℂ) * ((q + 1) / Complex.I) +
          ((Real.pi : ℂ) * Complex.I) * (1 - q) := by
      exact congrArg
        (fun z : ℂ => (Real.pi : ℂ) * z +
          ((Real.pi : ℂ) * Complex.I) * (1 - q))
        (cotangent_exp_ratio_cancel_denominator q hq)
    _ =
        (Real.pi : ℂ) * (-((q + 1) * Complex.I)) +
          ((Real.pi : ℂ) * Complex.I) * (1 - q) := by
      exact congrArg
        (fun z : ℂ => (Real.pi : ℂ) * z +
          ((Real.pi : ℂ) * Complex.I) * (1 - q))
        (Complex.div_I (q + 1))
    _ = -((2 : ℂ) * (Real.pi : ℂ) * Complex.I) * q :=
      cotangent_upper_linear_numerator_identity q

/-- Product-form upper cotangent ratio identity. -/
theorem cotangent_upper_exp_ratio_identity
    (q : ℂ)
    (hq : q ≠ 1) :
    (Real.pi : ℂ) * ((q + 1) / (Complex.I * (1 - q))) +
        (Real.pi : ℂ) * Complex.I =
      -((2 : ℂ) * (Real.pi : ℂ) * Complex.I) *
        (q / (1 - q)) := by
  have hdiv := cotangent_upper_exp_ratio_identity_div q hq
  calc
    (Real.pi : ℂ) * ((q + 1) / (Complex.I * (1 - q))) +
        (Real.pi : ℂ) * Complex.I =
        (-((2 : ℂ) * (Real.pi : ℂ) * Complex.I) * q) / (1 - q) :=
      hdiv
    _ =
        -((2 : ℂ) * (Real.pi : ℂ) * Complex.I) * (q / (1 - q)) := by
      exact mul_div_assoc
        (-((2 : ℂ) * (Real.pi : ℂ) * Complex.I)) q (1 - q)

/-- The lower finite-strip exponential is the inverse of the small lower
cotangent parameter. -/
theorem cotangent_lower_exp_eq_inv_lowerQ
    (x T : ℝ) :
    Complex.exp
      ((2 : ℂ) * (Real.pi : ℂ) * Complex.I *
        ((x : ℂ) - (T : ℂ) * Complex.I)) =
      (Complex.finiteAbelPlanaCotangentLowerQ x T)⁻¹ := by
  let E : ℂ :=
    (2 : ℂ) * (Real.pi : ℂ) * Complex.I *
      ((x : ℂ) - (T : ℂ) * Complex.I)
  calc
    Complex.exp
      ((2 : ℂ) * (Real.pi : ℂ) * Complex.I *
        ((x : ℂ) - (T : ℂ) * Complex.I)) =
        Complex.exp E := rfl
    _ = ((Complex.exp E)⁻¹)⁻¹ := by
      exact (inv_inv (Complex.exp E)).symm
    _ = (Complex.exp (-E))⁻¹ := by
      exact (congrArg Inv.inv (Complex.exp_neg E)).symm
    _ = (Complex.finiteAbelPlanaCotangentLowerQ x T)⁻¹ := rfl

/-- Cancels the shared `1` in `a + 1 - (1 + b)`. -/
theorem add_one_sub_one_add
    (a b : ℂ) :
    a + 1 + -(1 + b) = a - b := by
  calc
    a + 1 + -(1 + b) =
        a + (1 + -(1 + b)) := by
      exact add_assoc a 1 (-(1 + b))
    _ = a + (1 + (-1 + -b)) := by
      exact congrArg (fun z : ℂ => a + (1 + z))
        (neg_add (1 : ℂ) b)
    _ = a + ((1 + -1) + -b) := by
      exact congrArg (fun z : ℂ => a + z)
        (add_assoc (1 : ℂ) (-1) (-b)).symm
    _ = a + (0 + -b) := by
      exact congrArg (fun z : ℂ => a + (z + -b))
        (add_neg_cancel (1 : ℂ))
    _ = a + -b := by
      exact congrArg (fun z : ℂ => a + z) (zero_add (-b))
    _ = a - b := by
      exact (sub_eq_add_neg a b).symm

/-- First reciprocal-ratio expansion: multiplying the inverse numerator by
`1 - q` gives `q⁻¹ - q`. -/
theorem cotangent_inverse_ratio_left_product
    (q : ℂ)
    (hq0 : q ≠ 0) :
    (q⁻¹ + 1) * (1 - q) = q⁻¹ - q := by
  calc
    (q⁻¹ + 1) * (1 - q) =
        (q⁻¹ + 1) * 1 + (q⁻¹ + 1) * (-q) := by
      exact left_distrib (q⁻¹ + 1) 1 (-q)
    _ = (q⁻¹ + 1) + (q⁻¹ + 1) * (-q) := by
      exact congrArg (fun z : ℂ => z + (q⁻¹ + 1) * (-q))
        (mul_one (q⁻¹ + 1))
    _ = (q⁻¹ + 1) + -((q⁻¹ + 1) * q) := by
      exact congrArg (fun z : ℂ => (q⁻¹ + 1) + z)
        (mul_neg (q⁻¹ + 1) q)
    _ = (q⁻¹ + 1) + -(q⁻¹ * q + 1 * q) := by
      exact congrArg
        (fun z : ℂ => (q⁻¹ + 1) + -z)
        (right_distrib q⁻¹ 1 q)
    _ = (q⁻¹ + 1) + -(1 + 1 * q) := by
      exact congrArg
        (fun z : ℂ => (q⁻¹ + 1) + -(z + 1 * q))
        (inv_mul_cancel₀ hq0)
    _ = (q⁻¹ + 1) + -(1 + q) := by
      exact congrArg
        (fun z : ℂ => (q⁻¹ + 1) + -(1 + z))
        (one_mul q)
    _ = q⁻¹ - q := by
      exact add_one_sub_one_add q⁻¹ q

/-- Second reciprocal-ratio expansion: multiplying the direct numerator by
`1 - q⁻¹` gives `q - q⁻¹`. -/
theorem cotangent_inverse_ratio_right_product
    (q : ℂ)
    (hq0 : q ≠ 0) :
    (q + 1) * (1 - q⁻¹) = q - q⁻¹ := by
  calc
    (q + 1) * (1 - q⁻¹) =
        (q + 1) * 1 + (q + 1) * (-q⁻¹) := by
      exact left_distrib (q + 1) 1 (-q⁻¹)
    _ = (q + 1) + (q + 1) * (-q⁻¹) := by
      exact congrArg (fun z : ℂ => z + (q + 1) * (-q⁻¹))
        (mul_one (q + 1))
    _ = (q + 1) + -((q + 1) * q⁻¹) := by
      exact congrArg (fun z : ℂ => (q + 1) + z)
        (mul_neg (q + 1) q⁻¹)
    _ = (q + 1) + -(q * q⁻¹ + 1 * q⁻¹) := by
      exact congrArg
        (fun z : ℂ => (q + 1) + -z)
        (right_distrib q 1 q⁻¹)
    _ = (q + 1) + -(1 + 1 * q⁻¹) := by
      exact congrArg
        (fun z : ℂ => (q + 1) + -(z + 1 * q⁻¹))
        (mul_inv_cancel₀ hq0)
    _ = (q + 1) + -(1 + q⁻¹) := by
      exact congrArg
        (fun z : ℂ => (q + 1) + -(1 + z))
        (one_mul q⁻¹)
    _ = q - q⁻¹ := by
      exact add_one_sub_one_add q q⁻¹

/-- Negating the direct reciprocal expansion gives the left reciprocal
expansion with the cotangent `I` factor. -/
theorem cotangent_inverse_ratio_cross_product
    (q : ℂ)
    (hq0 : q ≠ 0) :
    Complex.I * (q⁻¹ - q) =
      (-(q + 1)) * (Complex.I * (1 - q⁻¹)) := by
  have hright :
      (q + 1) * (1 - q⁻¹) = q - q⁻¹ :=
    cotangent_inverse_ratio_right_product q hq0
  calc
    Complex.I * (q⁻¹ - q) =
        Complex.I * (-(q - q⁻¹)) := by
      exact congrArg (fun z : ℂ => Complex.I * z) (neg_sub q q⁻¹).symm
    _ = -(Complex.I * (q - q⁻¹)) := by
      exact mul_neg Complex.I (q - q⁻¹)
    _ = -(Complex.I * ((q + 1) * (1 - q⁻¹))) := by
      exact congrArg (fun z : ℂ => -(Complex.I * z)) hright.symm
    _ = -(((q + 1) * Complex.I) * (1 - q⁻¹)) := by
      exact congrArg Neg.neg
        (by
          calc
            Complex.I * ((q + 1) * (1 - q⁻¹)) =
                (Complex.I * (q + 1)) * (1 - q⁻¹) :=
              (mul_assoc Complex.I (q + 1) (1 - q⁻¹)).symm
            _ = ((q + 1) * Complex.I) * (1 - q⁻¹) := by
              exact congrArg (fun z : ℂ => z * (1 - q⁻¹))
                (mul_comm Complex.I (q + 1)))
    _ = -((q + 1) * (Complex.I * (1 - q⁻¹))) := by
      exact congrArg Neg.neg (mul_assoc (q + 1) Complex.I (1 - q⁻¹))
    _ = (-(q + 1)) * (Complex.I * (1 - q⁻¹)) := by
      exact (neg_mul (q + 1) (Complex.I * (1 - q⁻¹))).symm

/-- The reciprocal cotangent ratio is the negative of the upper ratio written
with the small parameter. -/
theorem cotangent_lower_inverse_ratio_eq_neg_upper_ratio
    (q : ℂ)
    (hq0 : q ≠ 0)
    (hq1 : q ≠ 1) :
    (q⁻¹ + 1) / (Complex.I * (1 - q⁻¹)) =
      -((q + 1) / (Complex.I * (1 - q))) := by
  have hden : (1 : ℂ) - q ≠ 0 := by
    intro hzero
    have hone_eq_q : (1 : ℂ) = q := sub_eq_zero.mp hzero
    exact hq1 hone_eq_q.symm
  have hden_inv : (1 : ℂ) - q⁻¹ ≠ 0 := by
    intro hzero
    have hone_eq_inv : (1 : ℂ) = q⁻¹ := sub_eq_zero.mp hzero
    have hq_eq_one : q = 1 := by
      calc
        q = (q⁻¹)⁻¹ := by
          exact (inv_inv q).symm
        _ = (1 : ℂ)⁻¹ := by
          exact congrArg Inv.inv hone_eq_inv.symm
        _ = 1 := inv_one
    exact hq1 hq_eq_one
  have hIden : Complex.I * ((1 : ℂ) - q) ≠ 0 :=
    mul_ne_zero Complex.I_ne_zero hden
  have hIinvden : Complex.I * ((1 : ℂ) - q⁻¹) ≠ 0 :=
    mul_ne_zero Complex.I_ne_zero hden_inv
  have hneg :
      -((q + 1) / (Complex.I * (1 - q))) =
        (-(q + 1)) / (Complex.I * (1 - q)) := by
    exact (neg_div (Complex.I * (1 - q)) (q + 1)).symm
  calc
    (q⁻¹ + 1) / (Complex.I * (1 - q⁻¹)) =
        (-(q + 1)) / (Complex.I * (1 - q)) := by
      apply (div_eq_div_iff hIinvden hIden).mpr
      calc
        (q⁻¹ + 1) * (Complex.I * (1 - q)) =
            Complex.I * ((q⁻¹ + 1) * (1 - q)) := by
          calc
            (q⁻¹ + 1) * (Complex.I * (1 - q)) =
                ((q⁻¹ + 1) * Complex.I) * (1 - q) :=
              (mul_assoc (q⁻¹ + 1) Complex.I (1 - q)).symm
            _ = (Complex.I * (q⁻¹ + 1)) * (1 - q) := by
              exact congrArg (fun z : ℂ => z * (1 - q))
                (mul_comm (q⁻¹ + 1) Complex.I)
            _ = Complex.I * ((q⁻¹ + 1) * (1 - q)) :=
              mul_assoc Complex.I (q⁻¹ + 1) (1 - q)
        _ = Complex.I * (q⁻¹ - q) := by
          exact congrArg (fun z : ℂ => Complex.I * z)
            (cotangent_inverse_ratio_left_product q hq0)
        _ = (-(q + 1)) * (Complex.I * (1 - q⁻¹)) := by
          exact cotangent_inverse_ratio_cross_product q hq0
    _ = -((q + 1) / (Complex.I * (1 - q))) := hneg.symm

/-- Lower cotangent exponential ratio written with the small lower parameter. -/
theorem cotangent_lower_exp_ratio_identity
    (q : ℂ)
    (hq0 : q ≠ 0)
    (hq1 : q ≠ 1) :
    (Real.pi : ℂ) * ((q⁻¹ + 1) / (Complex.I * (1 - q⁻¹))) -
        (Real.pi : ℂ) * Complex.I =
      ((2 : ℂ) * (Real.pi : ℂ) * Complex.I) *
        (q / (1 - q)) := by
  have hratio :
      (q⁻¹ + 1) / (Complex.I * (1 - q⁻¹)) =
        -((q + 1) / (Complex.I * (1 - q))) :=
    cotangent_lower_inverse_ratio_eq_neg_upper_ratio q hq0 hq1
  have hupper :
      (Real.pi : ℂ) * ((q + 1) / (Complex.I * (1 - q))) +
          (Real.pi : ℂ) * Complex.I =
        -((2 : ℂ) * (Real.pi : ℂ) * Complex.I) *
          (q / (1 - q)) :=
    cotangent_upper_exp_ratio_identity q hq1
  calc
    (Real.pi : ℂ) * ((q⁻¹ + 1) / (Complex.I * (1 - q⁻¹))) -
        (Real.pi : ℂ) * Complex.I =
        (Real.pi : ℂ) * (-((q + 1) / (Complex.I * (1 - q)))) -
          (Real.pi : ℂ) * Complex.I := by
      exact congrArg
        (fun w : ℂ => (Real.pi : ℂ) * w - (Real.pi : ℂ) * Complex.I)
        hratio
    _ =
        -((Real.pi : ℂ) * ((q + 1) / (Complex.I * (1 - q))) +
          (Real.pi : ℂ) * Complex.I) := by
      calc
        (Real.pi : ℂ) * (-((q + 1) / (Complex.I * (1 - q)))) -
            (Real.pi : ℂ) * Complex.I =
            -((Real.pi : ℂ) * ((q + 1) / (Complex.I * (1 - q)))) -
              (Real.pi : ℂ) * Complex.I := by
          exact congrArg
            (fun z : ℂ => z - (Real.pi : ℂ) * Complex.I)
            (mul_neg (Real.pi : ℂ) ((q + 1) / (Complex.I * (1 - q))))
        _ =
            -((Real.pi : ℂ) * ((q + 1) / (Complex.I * (1 - q)))) +
              -((Real.pi : ℂ) * Complex.I) := by
          exact sub_eq_add_neg
            (-((Real.pi : ℂ) * ((q + 1) / (Complex.I * (1 - q)))))
            ((Real.pi : ℂ) * Complex.I)
        _ =
            -((Real.pi : ℂ) * ((q + 1) / (Complex.I * (1 - q))) +
              (Real.pi : ℂ) * Complex.I) := by
          exact (neg_add
            ((Real.pi : ℂ) * ((q + 1) / (Complex.I * (1 - q))))
            ((Real.pi : ℂ) * Complex.I)).symm
    _ =
        -(-((2 : ℂ) * (Real.pi : ℂ) * Complex.I) *
          (q / (1 - q))) := by
      exact congrArg Neg.neg hupper
    _ =
        ((2 : ℂ) * (Real.pi : ℂ) * Complex.I) *
          (q / (1 - q)) := by
      calc
        -(-((2 : ℂ) * (Real.pi : ℂ) * Complex.I) *
          (q / (1 - q))) =
            -(-(((2 : ℂ) * (Real.pi : ℂ) * Complex.I) *
              (q / (1 - q)))) := by
          exact congrArg Neg.neg
            (neg_mul ((2 : ℂ) * (Real.pi : ℂ) * Complex.I)
              (q / (1 - q)))
        _ =
            ((2 : ℂ) * (Real.pi : ℂ) * Complex.I) *
              (q / (1 - q)) := by
          exact neg_neg
            (((2 : ℂ) * (Real.pi : ℂ) * Complex.I) * (q / (1 - q)))

/-- Exact upper-half-plane exponential formula for the finite Abel-Plana
cotangent remainder.

This is the owner-level algebraic rewrite behind
`‖π cot(π(x+iT)) + π i‖`: after applying `Complex.cot_pi_eq_exp_ratio`, the
non-decaying constant term is `-π i` and the displayed quotient is the
geometric remainder. -/
theorem finiteAbelPlanaCotangentKernel_upper_exp_formula
    (x T : ℝ)
    (hT : 0 < T) :
    Complex.finiteAbelPlanaCotangentKernel
        ((x : ℂ) + (T : ℂ) * Complex.I) +
      (Real.pi : ℂ) * Complex.I =
        -((2 : ℂ) * (Real.pi : ℂ) * Complex.I) *
          (Complex.finiteAbelPlanaCotangentUpperQ x T /
            (1 - Complex.finiteAbelPlanaCotangentUpperQ x T)) := by
  let z : ℂ := (x : ℂ) + (T : ℂ) * Complex.I
  let q : ℂ := Complex.finiteAbelPlanaCotangentUpperQ x T
  have hq : q ≠ 1 := Complex.finiteAbelPlanaCotangentUpperQ_ne_one x T hT
  have hcot :
      (Real.pi : ℂ) * Complex.cot ((Real.pi : ℂ) * z) +
          (Real.pi : ℂ) * Complex.I =
        (Real.pi : ℂ) * ((q + 1) / (Complex.I * (1 - q))) +
          (Real.pi : ℂ) * Complex.I := by
    exact congrArg
      (fun w : ℂ => (Real.pi : ℂ) * w + (Real.pi : ℂ) * Complex.I)
      (Complex.cot_pi_eq_exp_ratio z)
  calc
    Complex.finiteAbelPlanaCotangentKernel
        ((x : ℂ) + (T : ℂ) * Complex.I) +
      (Real.pi : ℂ) * Complex.I =
        (Real.pi : ℂ) * Complex.cot ((Real.pi : ℂ) * z) +
          (Real.pi : ℂ) * Complex.I := rfl
    _ =
        (Real.pi : ℂ) * ((q + 1) / (Complex.I * (1 - q))) +
          (Real.pi : ℂ) * Complex.I := hcot
    _ =
        -((2 : ℂ) * (Real.pi : ℂ) * Complex.I) *
          (q / (1 - q)) :=
      cotangent_upper_exp_ratio_identity q hq
    _ =
        -((2 : ℂ) * (Real.pi : ℂ) * Complex.I) *
          (Complex.finiteAbelPlanaCotangentUpperQ x T /
            (1 - Complex.finiteAbelPlanaCotangentUpperQ x T)) := rfl

/-- Exact lower-half-plane exponential formula for the finite Abel-Plana
cotangent remainder.

This is the owner-level algebraic rewrite behind
`‖π cot(π(x-iT)) - π i‖`: after rewriting the cotangent formula using the
reciprocal exponential, the non-decaying constant term is `π i` and the
displayed quotient is the geometric remainder. -/
theorem finiteAbelPlanaCotangentKernel_lower_exp_formula
    (x T : ℝ)
    (hT : 0 < T) :
    Complex.finiteAbelPlanaCotangentKernel
        ((x : ℂ) - (T : ℂ) * Complex.I) -
      (Real.pi : ℂ) * Complex.I =
        ((2 : ℂ) * (Real.pi : ℂ) * Complex.I) *
          (Complex.finiteAbelPlanaCotangentLowerQ x T /
            (1 - Complex.finiteAbelPlanaCotangentLowerQ x T)) := by
  let z : ℂ := (x : ℂ) - (T : ℂ) * Complex.I
  let q : ℂ := Complex.finiteAbelPlanaCotangentLowerQ x T
  have hq0 : q ≠ 0 := by
    exact Complex.exp_ne_zero
      (-((2 : ℂ) * (Real.pi : ℂ) * Complex.I * z))
  have hq1 : q ≠ 1 :=
    Complex.finiteAbelPlanaCotangentLowerQ_ne_one x T hT
  have hexp :
      Complex.exp ((2 : ℂ) * (Real.pi : ℂ) * Complex.I * z) = q⁻¹ :=
    cotangent_lower_exp_eq_inv_lowerQ x T
  have hcot :
      (Real.pi : ℂ) * Complex.cot ((Real.pi : ℂ) * z) -
          (Real.pi : ℂ) * Complex.I =
        (Real.pi : ℂ) * ((q⁻¹ + 1) / (Complex.I * (1 - q⁻¹))) -
          (Real.pi : ℂ) * Complex.I := by
    exact congrArg
      (fun w : ℂ => (Real.pi : ℂ) * w - (Real.pi : ℂ) * Complex.I)
      ((Complex.cot_pi_eq_exp_ratio z).trans
        (congrArg
          (fun u : ℂ => (u + 1) / (Complex.I * (1 - u)))
          hexp))
  calc
    Complex.finiteAbelPlanaCotangentKernel
        ((x : ℂ) - (T : ℂ) * Complex.I) -
      (Real.pi : ℂ) * Complex.I =
        (Real.pi : ℂ) * Complex.cot ((Real.pi : ℂ) * z) -
          (Real.pi : ℂ) * Complex.I := rfl
    _ =
        (Real.pi : ℂ) * ((q⁻¹ + 1) / (Complex.I * (1 - q⁻¹))) -
          (Real.pi : ℂ) * Complex.I := hcot
    _ =
        ((2 : ℂ) * (Real.pi : ℂ) * Complex.I) *
          (q / (1 - q)) :=
      cotangent_lower_exp_ratio_identity q hq0 hq1
    _ =
        ((2 : ℂ) * (Real.pi : ℂ) * Complex.I) *
          (Complex.finiteAbelPlanaCotangentLowerQ x T /
            (1 - Complex.finiteAbelPlanaCotangentLowerQ x T)) := rfl

/-- Upper vertical-axis cotangent exponential formula for positive height.

This is the side-assembly specialization of
`finiteAbelPlanaCotangentKernel_upper_exp_formula` at horizontal coordinate
`0`. -/
theorem finiteAbelPlanaCotangentKernel_upper_vertical_exp_formula
    (t : ℝ)
    (ht : 0 < t) :
    Complex.finiteAbelPlanaCotangentKernel
        ((t : ℂ) * Complex.I) +
      (Real.pi : ℂ) * Complex.I =
        -((2 : ℂ) * (Real.pi : ℂ) * Complex.I) *
          (Complex.finiteAbelPlanaCotangentUpperQ 0 t /
            (1 - Complex.finiteAbelPlanaCotangentUpperQ 0 t)) := by
  have hformula :
      Complex.finiteAbelPlanaCotangentKernel
          ((0 : ℂ) + (t : ℂ) * Complex.I) +
        (Real.pi : ℂ) * Complex.I =
          -((2 : ℂ) * (Real.pi : ℂ) * Complex.I) *
            (Complex.finiteAbelPlanaCotangentUpperQ 0 t /
              (1 - Complex.finiteAbelPlanaCotangentUpperQ 0 t)) :=
    Complex.finiteAbelPlanaCotangentKernel_upper_exp_formula 0 t ht
  exact
    Eq.subst
      (motive := fun z : ℂ =>
        Complex.finiteAbelPlanaCotangentKernel z +
          (Real.pi : ℂ) * Complex.I =
            -((2 : ℂ) * (Real.pi : ℂ) * Complex.I) *
              (Complex.finiteAbelPlanaCotangentUpperQ 0 t /
                (1 - Complex.finiteAbelPlanaCotangentUpperQ 0 t)))
      (Complex.finiteAbelPlanaCotangentKernel_upper_vertical_arg t)
      hformula

/-- Lower vertical-axis cotangent exponential formula for positive height.

This is the side-assembly specialization of
`finiteAbelPlanaCotangentKernel_lower_exp_formula` at horizontal coordinate
`0`. -/
theorem finiteAbelPlanaCotangentKernel_lower_vertical_exp_formula
    (t : ℝ)
    (ht : 0 < t) :
    Complex.finiteAbelPlanaCotangentKernel
        (-((t : ℂ) * Complex.I)) -
      (Real.pi : ℂ) * Complex.I =
        ((2 : ℂ) * (Real.pi : ℂ) * Complex.I) *
          (Complex.finiteAbelPlanaCotangentLowerQ 0 t /
            (1 - Complex.finiteAbelPlanaCotangentLowerQ 0 t)) := by
  have hformula :
      Complex.finiteAbelPlanaCotangentKernel
          ((0 : ℂ) - (t : ℂ) * Complex.I) -
        (Real.pi : ℂ) * Complex.I =
          ((2 : ℂ) * (Real.pi : ℂ) * Complex.I) *
            (Complex.finiteAbelPlanaCotangentLowerQ 0 t /
              (1 - Complex.finiteAbelPlanaCotangentLowerQ 0 t)) :=
    Complex.finiteAbelPlanaCotangentKernel_lower_exp_formula 0 t ht
  exact
    Eq.subst
      (motive := fun z : ℂ =>
        Complex.finiteAbelPlanaCotangentKernel z -
          (Real.pi : ℂ) * Complex.I =
            ((2 : ℂ) * (Real.pi : ℂ) * Complex.I) *
              (Complex.finiteAbelPlanaCotangentLowerQ 0 t /
                (1 - Complex.finiteAbelPlanaCotangentLowerQ 0 t)))
      (Complex.finiteAbelPlanaCotangentKernel_lower_vertical_arg t)
      hformula

/-- Scalar geometric denominator bound for the cotangent exponential
remainder. -/
theorem norm_div_one_sub_le_two_mul_norm
    {q : ℂ}
    (hq : ‖q‖ ≤ (1 / 2 : ℝ)) :
    ‖q / (1 - q)‖ ≤ 2 * ‖q‖ := by
  have htriangle :
      ‖(1 : ℂ)‖ ≤ ‖(1 : ℂ) - q‖ + ‖q‖ := by
    calc
      ‖(1 : ℂ)‖ =
          ‖((1 : ℂ) - q) + q‖ := by
        exact congrArg norm (sub_add_cancel (1 : ℂ) q).symm
      _ ≤ ‖(1 : ℂ) - q‖ + ‖q‖ :=
        norm_add_le ((1 : ℂ) - q) q
  have hden_half : (1 / 2 : ℝ) ≤ ‖(1 : ℂ) - q‖ := by
    have hone_norm : ‖(1 : ℂ)‖ = (1 : ℝ) := norm_one
    have hone_le :
        (1 : ℝ) ≤ ‖(1 : ℂ) - q‖ + ‖q‖ :=
      Eq.subst
        (motive := fun x : ℝ => x ≤ ‖(1 : ℂ) - q‖ + ‖q‖)
        hone_norm
        htriangle
    have hsub_le : (1 : ℝ) - ‖q‖ ≤ ‖(1 : ℂ) - q‖ :=
      (sub_le_iff_le_add).mpr hone_le
    have hhalf_le_sub : (1 / 2 : ℝ) ≤ 1 - ‖q‖ := by
      calc
        (1 / 2 : ℝ) = 1 - (1 / 2 : ℝ) := by
          exact (sub_half (1 : ℝ)).symm
        _ ≤ 1 - ‖q‖ :=
          sub_le_sub_left hq 1
    exact hhalf_le_sub.trans hsub_le
  have hden_pos : 0 < ‖(1 : ℂ) - q‖ :=
    lt_of_lt_of_le one_half_pos hden_half
  have hnorm_div :
      ‖q / (1 - q)‖ = ‖q‖ / ‖(1 : ℂ) - q‖ := by
    exact norm_div q ((1 : ℂ) - q)
  have hmul :
      ‖q‖ ≤ (2 * ‖q‖) * ‖(1 : ℂ) - q‖ := by
    have htwo_den : (1 : ℝ) ≤ 2 * ‖(1 : ℂ) - q‖ := by
      have hscaled :
          2 * (1 / 2 : ℝ) ≤ 2 * ‖(1 : ℂ) - q‖ :=
        mul_le_mul_of_nonneg_left hden_half zero_le_two
      have hleft : 2 * (1 / 2 : ℝ) = 1 := by
        calc
          2 * (1 / 2 : ℝ) = (1 / 2 : ℝ) + (1 / 2 : ℝ) := by
            exact two_mul (1 / 2 : ℝ)
          _ = 1 := add_halves (1 : ℝ)
      exact
        Eq.subst
          (motive := fun x : ℝ => x ≤ 2 * ‖(1 : ℂ) - q‖)
          hleft
          hscaled
    calc
      ‖q‖ = ‖q‖ * 1 := by
        exact (mul_one ‖q‖).symm
      _ ≤ ‖q‖ * (2 * ‖(1 : ℂ) - q‖) :=
        mul_le_mul_of_nonneg_left htwo_den (norm_nonneg q)
      _ = (2 * ‖q‖) * ‖(1 : ℂ) - q‖ := by
        calc
          ‖q‖ * (2 * ‖(1 : ℂ) - q‖) =
              (‖q‖ * 2) * ‖(1 : ℂ) - q‖ := by
            exact (mul_assoc ‖q‖ 2 ‖(1 : ℂ) - q‖).symm
          _ = (2 * ‖q‖) * ‖(1 : ℂ) - q‖ := by
            exact congrArg
              (fun x : ℝ => x * ‖(1 : ℂ) - q‖)
              (mul_comm ‖q‖ 2)
  exact
    Eq.subst
      (motive := fun x : ℝ => x ≤ 2 * ‖q‖)
      hnorm_div.symm
      ((div_le_iff₀ hden_pos).mpr hmul)

/-- The finite-strip cotangent exponential parameter is eventually at most
`1/2` in norm. This is the boring asymptotic input behind the geometric
denominator estimate. -/
theorem eventually_norm_finiteAbelPlanaCotangentUpperQ_le_half
    (N : ℕ) :
    ∀ᶠ T : ℝ in atTop,
      ∀ x ∈ Set.uIoc (0 : ℝ) (N + 1 : ℝ),
        ‖Complex.finiteAbelPlanaCotangentUpperQ x T‖ ≤ (1 / 2 : ℝ) := by
  filter_upwards [eventually_ge_atTop
    (Real.log 2 / (2 * Real.pi))] with T hT x hx
  have hnorm :
      ‖Complex.finiteAbelPlanaCotangentUpperQ x T‖ =
        Real.exp (-(2 * Real.pi * T)) :=
    Complex.norm_finiteAbelPlanaCotangentUpperQ x T
  have hle : Real.exp (-(2 * Real.pi * T)) ≤ (1 / 2 : ℝ) := by
    have hscale_pos : 0 < (2 : ℝ) * Real.pi :=
      mul_pos two_pos Real.pi_pos
    have hlog_le_right :
        Real.log 2 ≤ T * ((2 : ℝ) * Real.pi) :=
      (div_le_iff₀ hscale_pos).mp hT
    have hlog_le :
        Real.log 2 ≤ (2 : ℝ) * Real.pi * T := by
      calc
        Real.log 2 ≤ T * ((2 : ℝ) * Real.pi) := hlog_le_right
        _ = (2 : ℝ) * Real.pi * T := by
          exact mul_comm T ((2 : ℝ) * Real.pi)
    have hneg_le :
        -(2 * Real.pi * T) ≤ -Real.log 2 :=
      neg_le_neg hlog_le
    have hexp_le :
        Real.exp (-(2 * Real.pi * T)) ≤ Real.exp (-Real.log 2) :=
      Real.exp_le_exp.mpr hneg_le
    have hexp_neg_log_two :
        Real.exp (-Real.log 2) = (1 / 2 : ℝ) := by
      calc
        Real.exp (-Real.log 2) = (Real.exp (Real.log 2))⁻¹ :=
          Real.exp_neg (Real.log 2)
        _ = (2 : ℝ)⁻¹ := by
          exact congrArg Inv.inv (Real.exp_log two_pos)
        _ = (1 / 2 : ℝ) := by
          exact inv_eq_one_div (2 : ℝ)
    exact hexp_le.trans_eq hexp_neg_log_two
  exact
    Eq.subst
      (motive := fun y : ℝ => y ≤ (1 / 2 : ℝ))
      hnorm.symm
      hle

/-- The scalar geometric denominator estimate specialized to the upper
finite-strip parameter. -/
theorem norm_finiteAbelPlanaCotangentUpperQ_div_one_sub_le
    (N : ℕ) :
    ∀ᶠ T : ℝ in atTop,
      ∀ x ∈ Set.uIoc (0 : ℝ) (N + 1 : ℝ),
        ‖Complex.finiteAbelPlanaCotangentUpperQ x T /
            (1 - Complex.finiteAbelPlanaCotangentUpperQ x T)‖ ≤
          2 * ‖Complex.finiteAbelPlanaCotangentUpperQ x T‖ := by
  filter_upwards [eventually_norm_finiteAbelPlanaCotangentUpperQ_le_half N] with
    T hT x hx
  exact norm_div_one_sub_le_two_mul_norm (hT x hx)

/-- The lower finite-strip cotangent exponential parameter is eventually at
most `1/2` in norm. -/
theorem eventually_norm_finiteAbelPlanaCotangentLowerQ_le_half
    (N : ℕ) :
    ∀ᶠ T : ℝ in atTop,
      ∀ x ∈ Set.uIoc (0 : ℝ) (N + 1 : ℝ),
        ‖Complex.finiteAbelPlanaCotangentLowerQ x T‖ ≤ (1 / 2 : ℝ) := by
  filter_upwards [eventually_ge_atTop
    (Real.log 2 / (2 * Real.pi))] with T hT x hx
  have hnorm :
      ‖Complex.finiteAbelPlanaCotangentLowerQ x T‖ =
        Real.exp (-(2 * Real.pi * T)) :=
    Complex.norm_finiteAbelPlanaCotangentLowerQ x T
  have hle : Real.exp (-(2 * Real.pi * T)) ≤ (1 / 2 : ℝ) := by
    have hscale_pos : 0 < (2 : ℝ) * Real.pi :=
      mul_pos two_pos Real.pi_pos
    have hlog_le_right :
        Real.log 2 ≤ T * ((2 : ℝ) * Real.pi) :=
      (div_le_iff₀ hscale_pos).mp hT
    have hlog_le :
        Real.log 2 ≤ (2 : ℝ) * Real.pi * T := by
      calc
        Real.log 2 ≤ T * ((2 : ℝ) * Real.pi) := hlog_le_right
        _ = (2 : ℝ) * Real.pi * T := by
          exact mul_comm T ((2 : ℝ) * Real.pi)
    have hneg_le :
        -(2 * Real.pi * T) ≤ -Real.log 2 :=
      neg_le_neg hlog_le
    have hexp_le :
        Real.exp (-(2 * Real.pi * T)) ≤ Real.exp (-Real.log 2) :=
      Real.exp_le_exp.mpr hneg_le
    have hexp_neg_log_two :
        Real.exp (-Real.log 2) = (1 / 2 : ℝ) := by
      calc
        Real.exp (-Real.log 2) = (Real.exp (Real.log 2))⁻¹ :=
          Real.exp_neg (Real.log 2)
        _ = (2 : ℝ)⁻¹ := by
          exact congrArg Inv.inv (Real.exp_log two_pos)
        _ = (1 / 2 : ℝ) := by
          exact inv_eq_one_div (2 : ℝ)
    exact hexp_le.trans_eq hexp_neg_log_two
  exact
    Eq.subst
      (motive := fun y : ℝ => y ≤ (1 / 2 : ℝ))
      hnorm.symm
      hle

/-- The scalar geometric denominator estimate specialized to the lower
finite-strip parameter. -/
theorem norm_finiteAbelPlanaCotangentLowerQ_div_one_sub_le
    (N : ℕ) :
    ∀ᶠ T : ℝ in atTop,
      ∀ x ∈ Set.uIoc (0 : ℝ) (N + 1 : ℝ),
        ‖Complex.finiteAbelPlanaCotangentLowerQ x T /
            (1 - Complex.finiteAbelPlanaCotangentLowerQ x T)‖ ≤
          2 * ‖Complex.finiteAbelPlanaCotangentLowerQ x T‖ := by
  filter_upwards [eventually_norm_finiteAbelPlanaCotangentLowerQ_le_half N] with
    T hT x hx
  exact norm_div_one_sub_le_two_mul_norm (hT x hx)

/-- The common finite-strip cotangent remainder estimate after the exact
half-plane exponential rewrite.

This is the owner estimate consumed by Abel-Plana horizontal-edge bounds.  It
contains no logarithmic summand and no contour assembly. -/
theorem norm_finiteAbelPlanaCotangentKernel_horizontal_remainder_le_exp
    (N : ℕ)
    (sgn : ℂ)
    (constantTerm : ℂ) :
    (sgn = Complex.I ∧ constantTerm = (Real.pi : ℂ) * Complex.I) ∨
      (sgn = -Complex.I ∧ constantTerm = -((Real.pi : ℂ) * Complex.I)) →
    ∀ᶠ T : ℝ in atTop,
      ∀ x ∈ Set.uIoc (0 : ℝ) (N + 1 : ℝ),
        ‖Complex.finiteAbelPlanaCotangentKernel
            ((x : ℂ) + (T : ℂ) * sgn) +
          constantTerm‖ ≤
          (4 * (Real.pi + 1)) *
            Real.exp (-(2 * Real.pi * |T|)) := by
  intro horientation
  rcases horientation with
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · filter_upwards [eventually_ge_atTop (Real.log 2 / (2 * Real.pi)),
      eventually_norm_finiteAbelPlanaCotangentUpperQ_le_half N,
      norm_finiteAbelPlanaCotangentUpperQ_div_one_sub_le N] with
      T hT_bound hsmall hfrac x hx
    have hT_pos : 0 < T := by
      have hscale_pos : 0 < (2 : ℝ) * Real.pi :=
        mul_pos two_pos Real.pi_pos
      have hthreshold_pos : 0 < Real.log 2 / (2 * Real.pi) :=
        div_pos (Real.log_pos one_lt_two) hscale_pos
      exact lt_of_lt_of_le hthreshold_pos hT_bound
    have hrewrite :=
      finiteAbelPlanaCotangentKernel_upper_exp_formula x T hT_pos
    have hnorm :
        ‖Complex.finiteAbelPlanaCotangentKernel
            ((x : ℂ) + (T : ℂ) * Complex.I) +
          (Real.pi : ℂ) * Complex.I‖ =
        ‖(2 : ℂ) * (Real.pi : ℂ) * Complex.I‖ *
          ‖Complex.finiteAbelPlanaCotangentUpperQ x T /
            (1 - Complex.finiteAbelPlanaCotangentUpperQ x T)‖ := by
      let A : ℂ := (2 : ℂ) * (Real.pi : ℂ) * Complex.I
      let F : ℂ :=
        Complex.finiteAbelPlanaCotangentUpperQ x T /
          (1 - Complex.finiteAbelPlanaCotangentUpperQ x T)
      have hrewrite_norm :
          ‖Complex.finiteAbelPlanaCotangentKernel
              ((x : ℂ) + (T : ℂ) * Complex.I) +
            (Real.pi : ℂ) * Complex.I‖ =
            ‖(-A) * F‖ := by
        exact congrArg norm hrewrite
      calc
        ‖Complex.finiteAbelPlanaCotangentKernel
            ((x : ℂ) + (T : ℂ) * Complex.I) +
          (Real.pi : ℂ) * Complex.I‖ =
            ‖(-A) * F‖ := hrewrite_norm
        _ = ‖-A‖ * ‖F‖ := norm_mul (-A) F
        _ = ‖A‖ * ‖F‖ := by
          exact congrArg (fun r : ℝ => r * ‖F‖) (norm_neg A)
    have hq :
        ‖Complex.finiteAbelPlanaCotangentUpperQ x T /
            (1 - Complex.finiteAbelPlanaCotangentUpperQ x T)‖ ≤
          2 * ‖Complex.finiteAbelPlanaCotangentUpperQ x T‖ :=
      by
        exact hfrac x hx
    have hqnorm_abs :
        ‖Complex.finiteAbelPlanaCotangentUpperQ x T‖ =
          Real.exp (-(2 * Real.pi * |T|)) := by
      have habs : |T| = T := abs_of_nonneg hT_pos.le
      have hexponent :
          -(2 * Real.pi * T) = -(2 * Real.pi * |T|) := by
        exact congrArg Neg.neg
          (congrArg (fun r : ℝ => 2 * Real.pi * r) habs.symm)
      exact
        Eq.trans
          (Complex.norm_finiteAbelPlanaCotangentUpperQ x T)
          (congrArg Real.exp hexponent)
    calc
      ‖Complex.finiteAbelPlanaCotangentKernel
          ((x : ℂ) + (T : ℂ) * Complex.I) +
        (Real.pi : ℂ) * Complex.I‖ =
          ‖(2 : ℂ) * (Real.pi : ℂ) * Complex.I‖ *
            ‖Complex.finiteAbelPlanaCotangentUpperQ x T /
              (1 - Complex.finiteAbelPlanaCotangentUpperQ x T)‖ := hnorm
      _ ≤ ‖(2 : ℂ) * (Real.pi : ℂ) * Complex.I‖ *
            (2 * ‖Complex.finiteAbelPlanaCotangentUpperQ x T‖) := by
        exact mul_le_mul_of_nonneg_left hq
          (norm_nonneg ((2 : ℂ) * (Real.pi : ℂ) * Complex.I))
      _ = (2 * ‖(2 : ℂ) * (Real.pi : ℂ) * Complex.I‖) *
            ‖Complex.finiteAbelPlanaCotangentUpperQ x T‖ := by
        calc
          ‖(2 : ℂ) * (Real.pi : ℂ) * Complex.I‖ *
              (2 * ‖Complex.finiteAbelPlanaCotangentUpperQ x T‖) =
            (‖(2 : ℂ) * (Real.pi : ℂ) * Complex.I‖ * 2) *
              ‖Complex.finiteAbelPlanaCotangentUpperQ x T‖ :=
              (mul_assoc
                ‖(2 : ℂ) * (Real.pi : ℂ) * Complex.I‖
                2
                ‖Complex.finiteAbelPlanaCotangentUpperQ x T‖).symm
          _ =
            (2 * ‖(2 : ℂ) * (Real.pi : ℂ) * Complex.I‖) *
              ‖Complex.finiteAbelPlanaCotangentUpperQ x T‖ := by
              exact congrArg
                (fun r : ℝ => r * ‖Complex.finiteAbelPlanaCotangentUpperQ x T‖)
                (mul_comm ‖(2 : ℂ) * (Real.pi : ℂ) * Complex.I‖ 2)
      _ ≤ (4 * (Real.pi + 1)) *
            ‖Complex.finiteAbelPlanaCotangentUpperQ x T‖ := by
        exact mul_le_mul_of_nonneg_right
          Complex.two_mul_norm_two_pi_I_le_four_pi_add_one
          (norm_nonneg (Complex.finiteAbelPlanaCotangentUpperQ x T))
      _ = (4 * (Real.pi + 1)) *
            Real.exp (-(2 * Real.pi * |T|)) := by
        exact congrArg (fun r : ℝ => (4 * (Real.pi + 1)) * r) hqnorm_abs
  · filter_upwards [eventually_ge_atTop (Real.log 2 / (2 * Real.pi)),
      norm_finiteAbelPlanaCotangentLowerQ_div_one_sub_le N] with
      T hT_bound hT x hx
    have hT_pos : 0 < T := by
      have hscale_pos : 0 < (2 : ℝ) * Real.pi :=
        mul_pos two_pos Real.pi_pos
      have hthreshold_pos : 0 < Real.log 2 / (2 * Real.pi) :=
        div_pos (Real.log_pos one_lt_two) hscale_pos
      exact lt_of_lt_of_le hthreshold_pos hT_bound
    have hrewrite :=
      finiteAbelPlanaCotangentKernel_lower_exp_formula x T hT_pos
    have hnorm :
        ‖Complex.finiteAbelPlanaCotangentKernel
            ((x : ℂ) - (T : ℂ) * Complex.I) -
          (Real.pi : ℂ) * Complex.I‖ =
        ‖(2 : ℂ) * (Real.pi : ℂ) * Complex.I‖ *
          ‖Complex.finiteAbelPlanaCotangentLowerQ x T /
            (1 - Complex.finiteAbelPlanaCotangentLowerQ x T)‖ := by
      let A : ℂ := (2 : ℂ) * (Real.pi : ℂ) * Complex.I
      let F : ℂ :=
        Complex.finiteAbelPlanaCotangentLowerQ x T /
          (1 - Complex.finiteAbelPlanaCotangentLowerQ x T)
      have hrewrite_norm :
          ‖Complex.finiteAbelPlanaCotangentKernel
              ((x : ℂ) - (T : ℂ) * Complex.I) -
            (Real.pi : ℂ) * Complex.I‖ =
            ‖A * F‖ := by
        exact congrArg norm hrewrite
      calc
        ‖Complex.finiteAbelPlanaCotangentKernel
            ((x : ℂ) - (T : ℂ) * Complex.I) -
          (Real.pi : ℂ) * Complex.I‖ =
            ‖A * F‖ := hrewrite_norm
        _ = ‖A‖ * ‖F‖ := norm_mul A F
    have hq :
        ‖Complex.finiteAbelPlanaCotangentLowerQ x T /
            (1 - Complex.finiteAbelPlanaCotangentLowerQ x T)‖ ≤
          2 * ‖Complex.finiteAbelPlanaCotangentLowerQ x T‖ :=
      by
        exact hT x hx
    have hqnorm_abs :
        ‖Complex.finiteAbelPlanaCotangentLowerQ x T‖ =
          Real.exp (-(2 * Real.pi * |T|)) := by
      have habs : |T| = T := abs_of_nonneg hT_pos.le
      have hexponent :
          -(2 * Real.pi * T) = -(2 * Real.pi * |T|) := by
        exact congrArg Neg.neg
          (congrArg (fun r : ℝ => 2 * Real.pi * r) habs.symm)
      exact
        Eq.trans
          (Complex.norm_finiteAbelPlanaCotangentLowerQ x T)
          (congrArg Real.exp hexponent)
    have htarget_norm :
        ‖Complex.finiteAbelPlanaCotangentKernel
            ((x : ℂ) + (T : ℂ) * (-Complex.I)) +
          -((Real.pi : ℂ) * Complex.I)‖ =
        ‖Complex.finiteAbelPlanaCotangentKernel
            ((x : ℂ) - (T : ℂ) * Complex.I) -
          (Real.pi : ℂ) * Complex.I‖ := by
      have harg :
          ((x : ℂ) + (T : ℂ) * (-Complex.I)) =
            ((x : ℂ) - (T : ℂ) * Complex.I) := by
        calc
          ((x : ℂ) + (T : ℂ) * (-Complex.I)) =
              (x : ℂ) + -((T : ℂ) * Complex.I) := by
            exact congrArg (fun z : ℂ => (x : ℂ) + z)
              (mul_neg (T : ℂ) Complex.I)
          _ = (x : ℂ) - (T : ℂ) * Complex.I := by
            exact (sub_eq_add_neg (x : ℂ) ((T : ℂ) * Complex.I)).symm
      have hleft :
          Complex.finiteAbelPlanaCotangentKernel
              ((x : ℂ) + (T : ℂ) * (-Complex.I)) +
            -((Real.pi : ℂ) * Complex.I) =
          Complex.finiteAbelPlanaCotangentKernel
              ((x : ℂ) - (T : ℂ) * Complex.I) -
            (Real.pi : ℂ) * Complex.I := by
        calc
          Complex.finiteAbelPlanaCotangentKernel
              ((x : ℂ) + (T : ℂ) * (-Complex.I)) +
            -((Real.pi : ℂ) * Complex.I) =
              Complex.finiteAbelPlanaCotangentKernel
                ((x : ℂ) - (T : ℂ) * Complex.I) +
              -((Real.pi : ℂ) * Complex.I) := by
            exact congrArg
              (fun z : ℂ =>
                Complex.finiteAbelPlanaCotangentKernel z +
                  -((Real.pi : ℂ) * Complex.I))
              harg
          _ =
              Complex.finiteAbelPlanaCotangentKernel
                ((x : ℂ) - (T : ℂ) * Complex.I) -
              (Real.pi : ℂ) * Complex.I := by
            exact (sub_eq_add_neg
              (Complex.finiteAbelPlanaCotangentKernel
                ((x : ℂ) - (T : ℂ) * Complex.I))
              ((Real.pi : ℂ) * Complex.I)).symm
      exact congrArg norm hleft
    calc
      ‖Complex.finiteAbelPlanaCotangentKernel
          ((x : ℂ) + (T : ℂ) * (-Complex.I)) +
        -((Real.pi : ℂ) * Complex.I)‖ =
          ‖Complex.finiteAbelPlanaCotangentKernel
            ((x : ℂ) - (T : ℂ) * Complex.I) -
          (Real.pi : ℂ) * Complex.I‖ := htarget_norm
      _ =
          ‖(2 : ℂ) * (Real.pi : ℂ) * Complex.I‖ *
            ‖Complex.finiteAbelPlanaCotangentLowerQ x T /
              (1 - Complex.finiteAbelPlanaCotangentLowerQ x T)‖ := hnorm
      _ ≤ ‖(2 : ℂ) * (Real.pi : ℂ) * Complex.I‖ *
            (2 * ‖Complex.finiteAbelPlanaCotangentLowerQ x T‖) := by
        exact mul_le_mul_of_nonneg_left hq
          (norm_nonneg ((2 : ℂ) * (Real.pi : ℂ) * Complex.I))
      _ = (2 * ‖(2 : ℂ) * (Real.pi : ℂ) * Complex.I‖) *
            ‖Complex.finiteAbelPlanaCotangentLowerQ x T‖ := by
        calc
          ‖(2 : ℂ) * (Real.pi : ℂ) * Complex.I‖ *
              (2 * ‖Complex.finiteAbelPlanaCotangentLowerQ x T‖) =
            (‖(2 : ℂ) * (Real.pi : ℂ) * Complex.I‖ * 2) *
              ‖Complex.finiteAbelPlanaCotangentLowerQ x T‖ :=
              (mul_assoc
                ‖(2 : ℂ) * (Real.pi : ℂ) * Complex.I‖
                2
                ‖Complex.finiteAbelPlanaCotangentLowerQ x T‖).symm
          _ =
            (2 * ‖(2 : ℂ) * (Real.pi : ℂ) * Complex.I‖) *
              ‖Complex.finiteAbelPlanaCotangentLowerQ x T‖ := by
              exact congrArg
                (fun r : ℝ => r * ‖Complex.finiteAbelPlanaCotangentLowerQ x T‖)
                (mul_comm ‖(2 : ℂ) * (Real.pi : ℂ) * Complex.I‖ 2)
      _ ≤ (4 * (Real.pi + 1)) *
            ‖Complex.finiteAbelPlanaCotangentLowerQ x T‖ := by
        exact mul_le_mul_of_nonneg_right
          Complex.two_mul_norm_two_pi_I_le_four_pi_add_one
          (norm_nonneg (Complex.finiteAbelPlanaCotangentLowerQ x T))
      _ = (4 * (Real.pi + 1)) *
            Real.exp (-(2 * Real.pi * |T|)) := by
        exact congrArg (fun r : ℝ => (4 * (Real.pi + 1)) * r) hqnorm_abs

/-- Lower-half-plane finite-strip cotangent remainder estimate. -/
theorem norm_finiteAbelPlanaCotangentKernel_lowerHorizontal_remainder_le_exp
    (N : ℕ) :
    ∀ᶠ T : ℝ in atTop,
      ∀ x ∈ Set.uIoc (0 : ℝ) (N + 1 : ℝ),
        ‖Complex.finiteAbelPlanaCotangentKernel
            ((x : ℂ) - (T : ℂ) * Complex.I) -
          (Real.pi : ℂ) * Complex.I‖ ≤
          (4 * (Real.pi + 1)) *
            Real.exp (-(2 * Real.pi * |T|)) := by
  have hbase :
      ∀ᶠ T : ℝ in atTop,
        ∀ x ∈ Set.uIoc (0 : ℝ) (N + 1 : ℝ),
          ‖Complex.finiteAbelPlanaCotangentKernel
              ((x : ℂ) + (T : ℂ) * (-Complex.I)) +
            (-((Real.pi : ℂ) * Complex.I))‖ ≤
            (4 * (Real.pi + 1)) *
              Real.exp (-(2 * Real.pi * |T|)) :=
    Complex.norm_finiteAbelPlanaCotangentKernel_horizontal_remainder_le_exp
      N (-Complex.I) (-((Real.pi : ℂ) * Complex.I))
      (Or.inr ⟨rfl, rfl⟩)
  filter_upwards [hbase] with T hT x hx
  have harg :
      ((x : ℂ) + (T : ℂ) * (-Complex.I)) =
        ((x : ℂ) - (T : ℂ) * Complex.I) := by
    calc
      (x : ℂ) + (T : ℂ) * (-Complex.I) =
          (x : ℂ) + -((T : ℂ) * Complex.I) := by
        exact congrArg (fun z : ℂ => (x : ℂ) + z)
          (mul_neg (T : ℂ) Complex.I)
      _ = (x : ℂ) - (T : ℂ) * Complex.I := by
        exact (sub_eq_add_neg (x : ℂ) ((T : ℂ) * Complex.I)).symm
  have hterm :
      Complex.finiteAbelPlanaCotangentKernel
            ((x : ℂ) + (T : ℂ) * (-Complex.I)) +
          (-((Real.pi : ℂ) * Complex.I)) =
        Complex.finiteAbelPlanaCotangentKernel
            ((x : ℂ) - (T : ℂ) * Complex.I) -
          (Real.pi : ℂ) * Complex.I := by
    have harg_transport :
        Complex.finiteAbelPlanaCotangentKernel
            ((x : ℂ) + (T : ℂ) * (-Complex.I)) =
          Complex.finiteAbelPlanaCotangentKernel
            ((x : ℂ) - (T : ℂ) * Complex.I) :=
      congrArg Complex.finiteAbelPlanaCotangentKernel harg
    calc
      Complex.finiteAbelPlanaCotangentKernel
            ((x : ℂ) + (T : ℂ) * (-Complex.I)) +
          (-((Real.pi : ℂ) * Complex.I)) =
        Complex.finiteAbelPlanaCotangentKernel
            ((x : ℂ) - (T : ℂ) * Complex.I) +
          (-((Real.pi : ℂ) * Complex.I)) := by
        exact congrArg
          (fun z : ℂ => z + (-((Real.pi : ℂ) * Complex.I)))
          harg_transport
      _ =
        Complex.finiteAbelPlanaCotangentKernel
            ((x : ℂ) - (T : ℂ) * Complex.I) -
          (Real.pi : ℂ) * Complex.I := by
        exact (sub_eq_add_neg
          (Complex.finiteAbelPlanaCotangentKernel
            ((x : ℂ) - (T : ℂ) * Complex.I))
          ((Real.pi : ℂ) * Complex.I)).symm
  exact
    Eq.subst
      (motive := fun z : ℂ =>
        ‖z‖ ≤
          (4 * (Real.pi + 1)) *
            Real.exp (-(2 * Real.pi * |T|)))
      hterm
      (hT x hx)

/-- Upper-half-plane finite-strip cotangent remainder estimate. -/
theorem norm_finiteAbelPlanaCotangentKernel_upperHorizontal_remainder_le_exp
    (N : ℕ) :
    ∀ᶠ T : ℝ in atTop,
      ∀ x ∈ Set.uIoc (0 : ℝ) (N + 1 : ℝ),
        ‖Complex.finiteAbelPlanaCotangentKernel
            ((x : ℂ) + (T : ℂ) * Complex.I) +
          (Real.pi : ℂ) * Complex.I‖ ≤
          (4 * (Real.pi + 1)) *
            Real.exp (-(2 * Real.pi * |T|)) := by
  exact
    Complex.norm_finiteAbelPlanaCotangentKernel_horizontal_remainder_le_exp
      N Complex.I ((Real.pi : ℂ) * Complex.I)
      (Or.inl ⟨rfl, rfl⟩)

end Complex

end

end LFunctions
end Boundary
