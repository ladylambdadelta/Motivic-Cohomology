import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.GammaBinetStirling.BinetAbelPlanaPrincipalValueResidueTheorem

/-!
# Vertical boundary limits for the finite-height Abel-Plana contour

This file owns the cotangent vertical denominator normalizations, vertical
principal-value remainder limits, and reconstruction of the named Abel-Plana
boundary faces.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped Topology
open Filter MeasureTheory

/-- Positivity of the real vertical Abel-Plana exponential height. -/
theorem Real.two_pi_mul_pos_of_pos
    {t : ℝ}
    (ht : 0 < t) :
    0 < (2 : ℝ) * Real.pi * t :=
  mul_pos (mul_pos zero_lt_two Real.pi_pos) ht

/-- The positive real exponential denominator in the Abel-Plana kernel is
nonzero. -/
theorem Complex.exp_two_pi_real_sub_one_ne_zero
    {t : ℝ}
    (ht : 0 < t) :
    Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1 ≠ 0 := by
  have hpos : 0 < (2 : ℝ) * Real.pi * t :=
    Real.two_pi_mul_pos_of_pos ht
  have hne : Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) ≠ 1 := by
    intro h
    have hre : Real.exp ((2 : ℝ) * Real.pi * t) = 1 := by
      calc
        Real.exp ((2 : ℝ) * Real.pi * t) =
            (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ)).re := by
          exact (Complex.exp_ofReal_re ((2 : ℝ) * Real.pi * t)).symm
        _ = (1 : ℂ).re := congrArg Complex.re h
        _ = 1 := rfl
    have hlog : (2 : ℝ) * Real.pi * t = 0 :=
      (Real.exp_eq_one_iff ((2 : ℝ) * Real.pi * t)).mp hre
    exact (ne_of_gt hpos) hlog
  exact sub_ne_zero.mpr hne

/-- Denominator normalization for the reciprocal exponential quotient in the
Abel-Plana cotangent kernel. -/
theorem Complex.inv_div_one_sub_inv_eq_sub_one_inv
    {E : ℂ}
    (hE : E ≠ 0) :
    E⁻¹ / (1 - E⁻¹) = (E - 1)⁻¹ := by
  have hone :
      1 - E⁻¹ = (E - 1) * E⁻¹ := by
    calc
      1 - E⁻¹ = E * E⁻¹ - E⁻¹ := by
        exact congrArg (fun u : ℂ => u - E⁻¹) (mul_inv_cancel₀ hE).symm
      _ = E * E⁻¹ - 1 * E⁻¹ := by
        exact congrArg (fun u : ℂ => E * E⁻¹ - u) (one_mul E⁻¹).symm
      _ = (E - 1) * E⁻¹ := by
        exact (sub_mul E 1 E⁻¹).symm
  calc
    E⁻¹ / (1 - E⁻¹) = E⁻¹ * (1 - E⁻¹)⁻¹ := by
      exact div_eq_mul_inv E⁻¹ (1 - E⁻¹)
    _ = E⁻¹ * ((E - 1) * E⁻¹)⁻¹ := by
      exact congrArg (fun u : ℂ => E⁻¹ * u⁻¹) hone
    _ = E⁻¹ * ((E⁻¹)⁻¹ * (E - 1)⁻¹) := by
      exact congrArg (fun u : ℂ => E⁻¹ * u)
        (mul_inv_rev (E - 1) E⁻¹)
    _ = E⁻¹ * (E * (E - 1)⁻¹) := by
      exact congrArg
        (fun u : ℂ => E⁻¹ * (u * (E - 1)⁻¹))
        (inv_inv E)
    _ = (E⁻¹ * E) * (E - 1)⁻¹ := by
      exact (mul_assoc E⁻¹ E (E - 1)⁻¹).symm
    _ = 1 * (E - 1)⁻¹ := by
      exact congrArg (fun u : ℂ => u * (E - 1)⁻¹) (inv_mul_cancel₀ hE)
    _ = (E - 1)⁻¹ := one_mul (E - 1)⁻¹

/-- Left multiplication transports the reciprocal-exponential denominator
normalization. -/
theorem Complex.mul_inv_div_one_sub_inv_eq_div_sub_one
    (K : ℂ)
    {E : ℂ}
    (hE : E ≠ 0) :
    K * (E⁻¹ / (1 - E⁻¹)) = K / (E - 1) := by
  calc
    K * (E⁻¹ / (1 - E⁻¹)) = K * (E - 1)⁻¹ := by
      exact congrArg (fun u : ℂ => K * u)
        (Complex.inv_div_one_sub_inv_eq_sub_one_inv hE)
    _ = K / (E - 1) := by
      exact (div_eq_mul_inv K (E - 1)).symm

/-- Negative left multiplication transports the reciprocal-exponential
denominator normalization. -/
theorem Complex.neg_mul_inv_div_one_sub_inv_eq_neg_div_sub_one
    (K : ℂ)
    {E : ℂ}
    (hE : E ≠ 0) :
    -K * (E⁻¹ / (1 - E⁻¹)) = -K / (E - 1) :=
  Complex.mul_inv_div_one_sub_inv_eq_div_sub_one (-K) hE

/-- The upper vertical cotangent exponent at the left side is the negative
real Abel-Plana height. -/
theorem Complex.two_pi_I_mul_leftUpperVertical_eq_neg_height
    (t : ℝ) :
    ((2 : ℂ) * (Real.pi : ℂ) * Complex.I *
        ((0 : ℂ) + (t : ℂ) * Complex.I)) =
      -(((2 : ℝ) * Real.pi * t : ℝ) : ℂ) := by
  have hzero :
      ((0 : ℂ) + (t : ℂ) * Complex.I) = (t : ℂ) * Complex.I :=
    zero_add ((t : ℂ) * Complex.I)
  have hscale :
      (2 : ℂ) * (Real.pi : ℂ) * Complex.I =
        Complex.I * (((2 : ℝ) * Real.pi : ℝ) : ℂ) := by
    calc
      (2 : ℂ) * (Real.pi : ℂ) * Complex.I =
          (((2 : ℝ) * Real.pi : ℝ) : ℂ) * Complex.I := by
        exact congrArg
          (fun u : ℂ => u * Complex.I)
          (Complex.ofReal_mul (2 : ℝ) Real.pi).symm
      _ = Complex.I * (((2 : ℝ) * Real.pi : ℝ) : ℂ) :=
        mul_comm (((2 : ℝ) * Real.pi : ℝ) : ℂ) Complex.I
  calc
    ((2 : ℂ) * (Real.pi : ℂ) * Complex.I *
        ((0 : ℂ) + (t : ℂ) * Complex.I)) =
        (Complex.I * (((2 : ℝ) * Real.pi : ℝ) : ℂ)) *
          ((t : ℂ) * Complex.I) := by
      exact congrArg₂ HMul.hMul hscale hzero
    _ = (((-((2 : ℝ) * Real.pi) * t : ℝ)) : ℂ) :=
      Complex.I_real_mul_real_mul_I_eq_neg_real_mul
        ((2 : ℝ) * Real.pi) t
    _ = -(((2 : ℝ) * Real.pi * t : ℝ) : ℂ) := by
      have hneg_mul :
          -((2 : ℝ) * Real.pi) * t = -(((2 : ℝ) * Real.pi) * t) :=
        neg_mul ((2 : ℝ) * Real.pi) t
      exact Eq.trans
        (congrArg (fun r : ℝ => (r : ℂ)) hneg_mul)
        (Complex.ofReal_neg (((2 : ℝ) * Real.pi) * t))

/-- The upper vertical cotangent exponent at an integer right side separates
into its integer period and negative real height. -/
theorem Complex.two_pi_I_mul_rightUpperVertical_eq_period_sub_height
    (M : ℕ)
    (t : ℝ) :
    ((2 : ℂ) * (Real.pi : ℂ) * Complex.I *
        (((M : ℝ) : ℂ) + (t : ℂ) * Complex.I)) =
      (((M : ℤ) : ℂ) * ((2 : ℂ) * (Real.pi : ℂ) * Complex.I)) -
        (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) := by
  have hleft :
      ((M : ℂ) * ((2 : ℂ) * (Real.pi : ℂ) * Complex.I)) =
        (((M : ℤ) : ℂ) * ((2 : ℂ) * (Real.pi : ℂ) * Complex.I)) := by
    exact congrArg
      (fun u : ℂ => u * ((2 : ℂ) * (Real.pi : ℂ) * Complex.I))
      (Int.cast_natCast M).symm
  have hheight :
      ((2 : ℂ) * (Real.pi : ℂ) * Complex.I *
        ((0 : ℂ) + (t : ℂ) * Complex.I)) =
        -(((2 : ℝ) * Real.pi * t : ℝ) : ℂ) :=
    Complex.two_pi_I_mul_leftUpperVertical_eq_neg_height t
  calc
    ((2 : ℂ) * (Real.pi : ℂ) * Complex.I *
        (((M : ℝ) : ℂ) + (t : ℂ) * Complex.I)) =
        ((2 : ℂ) * (Real.pi : ℂ) * Complex.I) * (M : ℂ) +
          ((2 : ℂ) * (Real.pi : ℂ) * Complex.I) *
            ((0 : ℂ) + (t : ℂ) * Complex.I) := by
      exact (mul_add
        ((2 : ℂ) * (Real.pi : ℂ) * Complex.I)
        (M : ℂ)
        ((t : ℂ) * Complex.I)).trans
        (congrArg₂ HAdd.hAdd rfl
          (congrArg
            (fun u : ℂ => ((2 : ℂ) * (Real.pi : ℂ) * Complex.I) * u)
            (zero_add ((t : ℂ) * Complex.I)).symm))
    _ = (M : ℂ) * ((2 : ℂ) * (Real.pi : ℂ) * Complex.I) +
          -(((2 : ℝ) * Real.pi * t : ℝ) : ℂ) := by
      exact congrArg₂ HAdd.hAdd
        (mul_comm ((2 : ℂ) * (Real.pi : ℂ) * Complex.I) (M : ℂ))
        hheight
    _ = (((M : ℤ) : ℂ) * ((2 : ℂ) * (Real.pi : ℂ) * Complex.I)) +
          -(((2 : ℝ) * Real.pi * t : ℝ) : ℂ) := by
      exact congrArg
        (fun u : ℂ => u + -(((2 : ℝ) * Real.pi * t : ℝ) : ℂ))
        hleft
    _ = (((M : ℤ) : ℂ) * ((2 : ℂ) * (Real.pi : ℂ) * Complex.I)) -
        (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) := by
      exact (sub_eq_add_neg
        (((M : ℤ) : ℂ) * ((2 : ℂ) * (Real.pi : ℂ) * Complex.I))
        (((2 : ℝ) * Real.pi * t : ℝ) : ℂ)).symm

/-- The lower vertical cotangent exponent at the left side is also the negative
real Abel-Plana height after applying the reciprocal-exponential sign. -/
theorem Complex.neg_two_pi_I_mul_leftLowerVertical_eq_neg_height
    (t : ℝ) :
    (-((2 : ℂ) * (Real.pi : ℂ) * Complex.I *
        ((0 : ℂ) - (t : ℂ) * Complex.I))) =
      -(((2 : ℝ) * Real.pi * t : ℝ) : ℂ) := by
  have hupper :
      ((2 : ℂ) * (Real.pi : ℂ) * Complex.I *
        ((0 : ℂ) + (t : ℂ) * Complex.I)) =
        -(((2 : ℝ) * Real.pi * t : ℝ) : ℂ) :=
    Complex.two_pi_I_mul_leftUpperVertical_eq_neg_height t
  have hpoint :
      ((0 : ℂ) - (t : ℂ) * Complex.I) =
        -((0 : ℂ) + (t : ℂ) * Complex.I) := by
    calc
      ((0 : ℂ) - (t : ℂ) * Complex.I) =
          -((t : ℂ) * Complex.I) := zero_sub ((t : ℂ) * Complex.I)
      _ = -((0 : ℂ) + (t : ℂ) * Complex.I) := by
        exact congrArg Neg.neg (zero_add ((t : ℂ) * Complex.I)).symm
  calc
    (-((2 : ℂ) * (Real.pi : ℂ) * Complex.I *
        ((0 : ℂ) - (t : ℂ) * Complex.I))) =
        -(((2 : ℂ) * (Real.pi : ℂ) * Complex.I) *
          -((0 : ℂ) + (t : ℂ) * Complex.I)) := by
      exact congrArg Neg.neg
        (congrArg
          (fun u : ℂ => ((2 : ℂ) * (Real.pi : ℂ) * Complex.I) * u)
          hpoint)
    _ = ((2 : ℂ) * (Real.pi : ℂ) * Complex.I) *
          ((0 : ℂ) + (t : ℂ) * Complex.I) := by
      calc
        -(((2 : ℂ) * (Real.pi : ℂ) * Complex.I) *
            -((0 : ℂ) + (t : ℂ) * Complex.I)) =
            -(-(((2 : ℂ) * (Real.pi : ℂ) * Complex.I) *
              ((0 : ℂ) + (t : ℂ) * Complex.I))) := by
          exact congrArg Neg.neg
            (mul_neg
              ((2 : ℂ) * (Real.pi : ℂ) * Complex.I)
              ((0 : ℂ) + (t : ℂ) * Complex.I))
        _ = ((2 : ℂ) * (Real.pi : ℂ) * Complex.I) *
              ((0 : ℂ) + (t : ℂ) * Complex.I) :=
          neg_neg (((2 : ℂ) * (Real.pi : ℂ) * Complex.I) *
            ((0 : ℂ) + (t : ℂ) * Complex.I))
    _ = -(((2 : ℝ) * Real.pi * t : ℝ) : ℂ) := hupper

/-- The lower vertical cotangent exponent at an integer right side separates
into the negative integer period and negative real height. -/
theorem Complex.neg_two_pi_I_mul_rightLowerVertical_eq_negPeriod_sub_height
    (M : ℕ)
    (t : ℝ) :
    (-((2 : ℂ) * (Real.pi : ℂ) * Complex.I *
        (((M : ℝ) : ℂ) - (t : ℂ) * Complex.I))) =
      -(((M : ℤ) : ℂ) * ((2 : ℂ) * (Real.pi : ℂ) * Complex.I)) -
        (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) := by
  have hleft :
      ((M : ℂ) * ((2 : ℂ) * (Real.pi : ℂ) * Complex.I)) =
        (((M : ℤ) : ℂ) * ((2 : ℂ) * (Real.pi : ℂ) * Complex.I)) := by
    exact congrArg
      (fun u : ℂ => u * ((2 : ℂ) * (Real.pi : ℂ) * Complex.I))
      (Int.cast_natCast M).symm
  have hlower :
      (-((2 : ℂ) * (Real.pi : ℂ) * Complex.I *
        ((0 : ℂ) - (t : ℂ) * Complex.I))) =
        -(((2 : ℝ) * Real.pi * t : ℝ) : ℂ) :=
    Complex.neg_two_pi_I_mul_leftLowerVertical_eq_neg_height t
  calc
    (-((2 : ℂ) * (Real.pi : ℂ) * Complex.I *
        (((M : ℝ) : ℂ) - (t : ℂ) * Complex.I))) =
        -(((2 : ℂ) * (Real.pi : ℂ) * Complex.I) * (M : ℂ) +
          ((2 : ℂ) * (Real.pi : ℂ) * Complex.I) *
            ((0 : ℂ) - (t : ℂ) * Complex.I)) := by
      exact congrArg Neg.neg
        ((mul_add
          ((2 : ℂ) * (Real.pi : ℂ) * Complex.I)
          (M : ℂ)
          (-((t : ℂ) * Complex.I))).trans
          (congrArg₂ HAdd.hAdd rfl
            (congrArg
              (fun u : ℂ => ((2 : ℂ) * (Real.pi : ℂ) * Complex.I) * u)
              (zero_sub ((t : ℂ) * Complex.I)).symm)))
    _ = -(((2 : ℂ) * (Real.pi : ℂ) * Complex.I) * (M : ℂ)) +
          -(((2 : ℂ) * (Real.pi : ℂ) * Complex.I) *
            ((0 : ℂ) - (t : ℂ) * Complex.I)) := by
      exact neg_add
        (((2 : ℂ) * (Real.pi : ℂ) * Complex.I) * (M : ℂ))
        (((2 : ℂ) * (Real.pi : ℂ) * Complex.I) *
          ((0 : ℂ) - (t : ℂ) * Complex.I))
    _ = -((M : ℂ) * ((2 : ℂ) * (Real.pi : ℂ) * Complex.I)) +
          -(((2 : ℝ) * Real.pi * t : ℝ) : ℂ) := by
      exact congrArg₂ HAdd.hAdd
        (congrArg Neg.neg
          (mul_comm ((2 : ℂ) * (Real.pi : ℂ) * Complex.I) (M : ℂ)))
        hlower
    _ = -(((M : ℤ) : ℂ) * ((2 : ℂ) * (Real.pi : ℂ) * Complex.I)) +
          -(((2 : ℝ) * Real.pi * t : ℝ) : ℂ) := by
      exact congrArg
        (fun u : ℂ => -u + -(((2 : ℝ) * Real.pi * t : ℝ) : ℂ))
        hleft
    _ = -(((M : ℤ) : ℂ) * ((2 : ℂ) * (Real.pi : ℂ) * Complex.I)) -
        (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) := by
      exact (sub_eq_add_neg
        (-(((M : ℤ) : ℂ) * ((2 : ℂ) * (Real.pi : ℂ) * Complex.I)))
        (((2 : ℝ) * Real.pi * t : ℝ) : ℂ)).symm

/-- Reflection of the left vertical parameter under `t ↦ -t`. -/
theorem Complex.I_mul_neg_real_eq_neg_I_mul
    (t : ℝ) :
    Complex.I * ((-t : ℝ) : ℂ) = -(Complex.I * (t : ℂ)) := by
  calc
    Complex.I * ((-t : ℝ) : ℂ) =
        Complex.I * (-(t : ℂ)) := by
      exact congrArg (fun u : ℂ => Complex.I * u) (Complex.ofReal_neg t)
    _ = -(Complex.I * (t : ℂ)) :=
      mul_neg Complex.I (t : ℂ)

/-- Reflection of the right vertical parameter under `t ↦ -t`. -/
theorem Complex.rightVertical_add_I_mul_neg_real_eq_sub_I_mul
    (M : ℕ)
    (t : ℝ) :
    (M : ℂ) + Complex.I * ((-t : ℝ) : ℂ) =
      (M : ℂ) - Complex.I * (t : ℂ) := by
  calc
    (M : ℂ) + Complex.I * ((-t : ℝ) : ℂ) =
        (M : ℂ) + -(Complex.I * (t : ℂ)) := by
      exact congrArg (fun u : ℂ => (M : ℂ) + u)
        (Complex.I_mul_neg_real_eq_neg_I_mul t)
    _ = (M : ℂ) - Complex.I * (t : ℂ) :=
      (sub_eq_add_neg (M : ℂ) (Complex.I * (t : ℂ))).symm

/-- Cancelling the normalized cotangent factor `K / D` against the residue
normalization factor `K⁻¹`. -/
theorem Complex.inv_mul_mul_div_cancel_left
    {K : ℂ}
    (hK : K ≠ 0)
    (D X : ℂ) :
    K⁻¹ * (X * (K / D)) = X / D := by
  calc
    K⁻¹ * (X * (K / D)) =
        K⁻¹ * (X * (K * D⁻¹)) := by
      exact congrArg
        (fun u : ℂ => K⁻¹ * (X * u))
        (div_eq_mul_inv K D)
    _ = K⁻¹ * ((X * K) * D⁻¹) := by
      exact congrArg
        (fun u : ℂ => K⁻¹ * u)
        (mul_assoc X K D⁻¹).symm
    _ = K⁻¹ * ((K * X) * D⁻¹) := by
      exact congrArg
        (fun u : ℂ => K⁻¹ * (u * D⁻¹))
        (mul_comm X K)
    _ = K⁻¹ * (K * (X * D⁻¹)) := by
      exact congrArg
        (fun u : ℂ => K⁻¹ * u)
        (mul_assoc K X D⁻¹)
    _ = (K⁻¹ * K) * (X * D⁻¹) := by
      exact (mul_assoc K⁻¹ K (X * D⁻¹)).symm
    _ = 1 * (X * D⁻¹) := by
      exact congrArg
        (fun u : ℂ => u * (X * D⁻¹))
        (inv_mul_cancel₀ hK)
    _ = X * D⁻¹ := one_mul (X * D⁻¹)
    _ = X / D := by
      exact (div_eq_mul_inv X D).symm

/-- Cancelling the normalized cotangent factor `-K / D` against the residue
normalization factor `K⁻¹`. -/
theorem Complex.inv_mul_mul_neg_div_cancel_left
    {K : ℂ}
    (hK : K ≠ 0)
    (D X : ℂ) :
    K⁻¹ * (X * (-K / D)) = -(X / D) := by
  calc
    K⁻¹ * (X * (-K / D)) =
        K⁻¹ * (X * (-(K / D))) := by
      exact congrArg
        (fun u : ℂ => K⁻¹ * (X * u))
        (neg_div D K)
    _ = K⁻¹ * (-(X * (K / D))) := by
      exact congrArg
        (fun u : ℂ => K⁻¹ * u)
        (mul_neg X (K / D))
    _ = -(K⁻¹ * (X * (K / D))) := by
      exact mul_neg K⁻¹ (X * (K / D))
    _ = -(X / D) := by
      exact congrArg Neg.neg
        (Complex.inv_mul_mul_div_cancel_left hK D X)

/-- The two vertical cotangent remainders assemble into the normalized
logarithmic jump quotient. -/
theorem Complex.normalized_twoHalf_logJump_algebra
    {K : ℂ}
    (hK : K ≠ 0)
    (C D A B : ℂ) :
    K⁻¹ * ((C * (B * (K / D))) + (C * (A * (-K / D)))) =
      -(C * ((A - B) / D)) := by
  have hleft :
      K⁻¹ * (C * (B * (K / D))) = (C * B) / D := by
    calc
      K⁻¹ * (C * (B * (K / D))) =
          K⁻¹ * ((C * B) * (K / D)) := by
        exact congrArg
          (fun u : ℂ => K⁻¹ * u)
          (mul_assoc C B (K / D)).symm
      _ = (C * B) / D :=
        Complex.inv_mul_mul_div_cancel_left hK D (C * B)
  have hright :
      K⁻¹ * (C * (A * (-K / D))) = -((C * A) / D) := by
    calc
      K⁻¹ * (C * (A * (-K / D))) =
          K⁻¹ * ((C * A) * (-K / D)) := by
        exact congrArg
          (fun u : ℂ => K⁻¹ * u)
          (mul_assoc C A (-K / D)).symm
      _ = -((C * A) / D) :=
        Complex.inv_mul_mul_neg_div_cancel_left hK D (C * A)
  have hcombine :
      (C * B) / D + -((C * A) / D) =
        -(C * ((A - B) / D)) := by
    calc
      (C * B) / D + -((C * A) / D) =
          (C * B) / D - (C * A) / D := by
        exact (sub_eq_add_neg ((C * B) / D) ((C * A) / D)).symm
      _ = (C * B - C * A) / D :=
        div_sub_div_same (C * B) (C * A) D
      _ = (C * (B - A)) / D := by
        exact congrArg
          (fun u : ℂ => u / D)
          (mul_sub C B A).symm
      _ = (C * (-(A - B))) / D := by
        exact congrArg
          (fun u : ℂ => (C * u) / D)
          (neg_sub A B).symm
      _ = (-(C * (A - B))) / D := by
        exact congrArg
          (fun u : ℂ => u / D)
          (mul_neg C (A - B))
      _ = -((C * (A - B)) / D) :=
        neg_div D (C * (A - B))
      _ = -(C * ((A - B) / D)) := by
        exact congrArg Neg.neg
          (mul_div_assoc C (A - B) D)
  calc
    K⁻¹ * ((C * (B * (K / D))) + (C * (A * (-K / D)))) =
        K⁻¹ * (C * (B * (K / D))) +
          K⁻¹ * (C * (A * (-K / D))) :=
      mul_add K⁻¹ (C * (B * (K / D))) (C * (A * (-K / D)))
    _ = (C * B) / D + -((C * A) / D) := by
      exact congrArg₂ HAdd.hAdd hleft hright
    _ = -(C * ((A - B) / D)) := hcombine

/-- The upper vertical Abel-Plana cotangent parameter at the left endpoint is
the reciprocal of the positive real exponential height. -/
theorem Complex.finiteAbelPlanaCotangentUpperQ_zero_eq_exp_height_inv
    (t : ℝ) :
    Complex.finiteAbelPlanaCotangentUpperQ 0 t =
      (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ))⁻¹ := by
  have harg :
      ((2 : ℂ) * (Real.pi : ℂ) * Complex.I *
          ((0 : ℂ) + (t : ℂ) * Complex.I)) =
        -(((2 : ℝ) * Real.pi * t : ℝ) : ℂ) :=
    Complex.two_pi_I_mul_leftUpperVertical_eq_neg_height t
  calc
    Complex.finiteAbelPlanaCotangentUpperQ 0 t =
        Complex.exp
          ((2 : ℂ) * (Real.pi : ℂ) * Complex.I *
            ((0 : ℂ) + (t : ℂ) * Complex.I)) := rfl
    _ = Complex.exp (-(((2 : ℝ) * Real.pi * t : ℝ) : ℂ)) :=
      congrArg Complex.exp harg
    _ = (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ))⁻¹ :=
      Complex.exp_neg (((2 : ℝ) * Real.pi * t : ℝ) : ℂ)

/-- The integer-shifted upper vertical Abel-Plana cotangent parameter has the
same reciprocal exponential height as the left endpoint. -/
theorem Complex.finiteAbelPlanaCotangentUpperQ_intShift_eq_exp_height_inv
    (M : ℕ)
    (t : ℝ) :
    Complex.finiteAbelPlanaCotangentUpperQ (M : ℝ) t =
      (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ))⁻¹ := by
  have harg :
      ((2 : ℂ) * (Real.pi : ℂ) * Complex.I *
          (((M : ℝ) : ℂ) + (t : ℂ) * Complex.I)) =
        (((M : ℤ) : ℂ) * ((2 : ℂ) * (Real.pi : ℂ) * Complex.I)) -
          (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) :=
    Complex.two_pi_I_mul_rightUpperVertical_eq_period_sub_height M t
  have hperiod :
      Complex.exp (((M : ℤ) : ℂ) * ((2 : ℂ) * (Real.pi : ℂ) * Complex.I)) = 1 :=
    Complex.exp_eq_one_iff.mpr ⟨(M : ℤ), rfl⟩
  calc
    Complex.finiteAbelPlanaCotangentUpperQ (M : ℝ) t =
        Complex.exp
          ((2 : ℂ) * (Real.pi : ℂ) * Complex.I *
            (((M : ℝ) : ℂ) + (t : ℂ) * Complex.I)) := rfl
    _ =
        Complex.exp
          ((((M : ℤ) : ℂ) * ((2 : ℂ) * (Real.pi : ℂ) * Complex.I)) -
            (((2 : ℝ) * Real.pi * t : ℝ) : ℂ)) :=
      congrArg Complex.exp harg
    _ =
        Complex.exp (((M : ℤ) : ℂ) * ((2 : ℂ) * (Real.pi : ℂ) * Complex.I)) /
          Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) :=
      Complex.exp_sub
        (((M : ℤ) : ℂ) * ((2 : ℂ) * (Real.pi : ℂ) * Complex.I))
        (((2 : ℝ) * Real.pi * t : ℝ) : ℂ)
    _ = 1 / Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) := by
      exact congrArg
        (fun u : ℂ => u / Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ))
        hperiod
    _ = (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ))⁻¹ :=
      one_div (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ))

/-- The lower vertical Abel-Plana cotangent parameter at the left endpoint is
the reciprocal of the positive real exponential height. -/
theorem Complex.finiteAbelPlanaCotangentLowerQ_zero_eq_exp_height_inv
    (t : ℝ) :
    Complex.finiteAbelPlanaCotangentLowerQ 0 t =
      (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ))⁻¹ := by
  have harg :
      (-((2 : ℂ) * (Real.pi : ℂ) * Complex.I *
          ((0 : ℂ) - (t : ℂ) * Complex.I))) =
        -(((2 : ℝ) * Real.pi * t : ℝ) : ℂ) :=
    Complex.neg_two_pi_I_mul_leftLowerVertical_eq_neg_height t
  calc
    Complex.finiteAbelPlanaCotangentLowerQ 0 t =
        Complex.exp
          (-((2 : ℂ) * (Real.pi : ℂ) * Complex.I *
            ((0 : ℂ) - (t : ℂ) * Complex.I))) := rfl
    _ = Complex.exp (-(((2 : ℝ) * Real.pi * t : ℝ) : ℂ)) :=
      congrArg Complex.exp harg
    _ = (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ))⁻¹ :=
      Complex.exp_neg (((2 : ℝ) * Real.pi * t : ℝ) : ℂ)

/-- The integer-shifted lower vertical Abel-Plana cotangent parameter has the
same reciprocal exponential height as the left endpoint. -/
theorem Complex.finiteAbelPlanaCotangentLowerQ_intShift_eq_exp_height_inv
    (M : ℕ)
    (t : ℝ) :
    Complex.finiteAbelPlanaCotangentLowerQ (M : ℝ) t =
      (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ))⁻¹ := by
  have harg :
      (-((2 : ℂ) * (Real.pi : ℂ) * Complex.I *
          (((M : ℝ) : ℂ) - (t : ℂ) * Complex.I))) =
        -(((M : ℤ) : ℂ) * ((2 : ℂ) * (Real.pi : ℂ) * Complex.I)) -
          (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) :=
    Complex.neg_two_pi_I_mul_rightLowerVertical_eq_negPeriod_sub_height M t
  have hbase :
      Complex.exp (((M : ℤ) : ℂ) * ((2 : ℂ) * (Real.pi : ℂ) * Complex.I)) = 1 :=
    Complex.exp_eq_one_iff.mpr ⟨(M : ℤ), rfl⟩
  have hperiod :
      Complex.exp (-(((M : ℤ) : ℂ) * ((2 : ℂ) * (Real.pi : ℂ) * Complex.I))) = 1 := by
    calc
      Complex.exp (-(((M : ℤ) : ℂ) * ((2 : ℂ) * (Real.pi : ℂ) * Complex.I))) =
          (Complex.exp (((M : ℤ) : ℂ) * ((2 : ℂ) * (Real.pi : ℂ) * Complex.I)))⁻¹ :=
        Complex.exp_neg (((M : ℤ) : ℂ) * ((2 : ℂ) * (Real.pi : ℂ) * Complex.I))
      _ = 1⁻¹ := congrArg Inv.inv hbase
      _ = 1 := inv_one
  calc
    Complex.finiteAbelPlanaCotangentLowerQ (M : ℝ) t =
        Complex.exp
          (-((2 : ℂ) * (Real.pi : ℂ) * Complex.I *
            (((M : ℝ) : ℂ) - (t : ℂ) * Complex.I))) := rfl
    _ =
        Complex.exp
          (-(((M : ℤ) : ℂ) * ((2 : ℂ) * (Real.pi : ℂ) * Complex.I)) -
            (((2 : ℝ) * Real.pi * t : ℝ) : ℂ)) :=
      congrArg Complex.exp harg
    _ =
        Complex.exp (-(((M : ℤ) : ℂ) * ((2 : ℂ) * (Real.pi : ℂ) * Complex.I))) /
          Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) :=
      Complex.exp_sub
        (-(((M : ℤ) : ℂ) * ((2 : ℂ) * (Real.pi : ℂ) * Complex.I)))
        (((2 : ℝ) * Real.pi * t : ℝ) : ℂ)
    _ = 1 / Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) := by
      exact congrArg
        (fun u : ℂ => u / Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ))
        hperiod
    _ = (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ))⁻¹ :=
      one_div (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ))

/-- Vertical-axis cotangent exponential denominator normalization.

The upper-half-plane cotangent remainder on `I*t` is the usual Abel-Plana
kernel denominator `(exp (2πt) - 1)⁻¹`. -/
theorem Complex.finiteAbelPlanaCotangentKernel_upper_vertical_expDenominator
    (t : ℝ)
    (ht : 0 < t) :
    Complex.finiteAbelPlanaCotangentKernel (Complex.I * (t : ℂ)) +
        (Real.pi : ℂ) * Complex.I =
      -((2 : ℂ) * (Real.pi : ℂ) * Complex.I) /
        (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1) := by
  have hupper :
      Complex.finiteAbelPlanaCotangentKernel ((t : ℂ) * Complex.I) +
          (Real.pi : ℂ) * Complex.I =
        -((2 : ℂ) * (Real.pi : ℂ) * Complex.I) *
          (Complex.finiteAbelPlanaCotangentUpperQ 0 t /
            (1 - Complex.finiteAbelPlanaCotangentUpperQ 0 t)) :=
    Complex.finiteAbelPlanaCotangentKernel_upper_vertical_exp_formula t ht
  have hden :
      -((2 : ℂ) * (Real.pi : ℂ) * Complex.I) *
          (Complex.finiteAbelPlanaCotangentUpperQ 0 t /
        (1 - Complex.finiteAbelPlanaCotangentUpperQ 0 t)) =
        -((2 : ℂ) * (Real.pi : ℂ) * Complex.I) /
          (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1) := by
    have hq :
        Complex.finiteAbelPlanaCotangentUpperQ 0 t =
          (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ))⁻¹ :=
      Complex.finiteAbelPlanaCotangentUpperQ_zero_eq_exp_height_inv t
    calc
      -((2 : ℂ) * (Real.pi : ℂ) * Complex.I) *
          (Complex.finiteAbelPlanaCotangentUpperQ 0 t /
        (1 - Complex.finiteAbelPlanaCotangentUpperQ 0 t)) =
        -((2 : ℂ) * (Real.pi : ℂ) * Complex.I) *
          ((Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ))⁻¹ /
        (1 - (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ))⁻¹)) := by
        exact congrArg
          (fun q : ℂ =>
            -((2 : ℂ) * (Real.pi : ℂ) * Complex.I) * (q / (1 - q)))
          hq
      _ =
        -((2 : ℂ) * (Real.pi : ℂ) * Complex.I) /
          (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1) :=
        Complex.neg_mul_inv_div_one_sub_inv_eq_neg_div_sub_one
          ((2 : ℂ) * (Real.pi : ℂ) * Complex.I)
          (Complex.exp_ne_zero (((2 : ℝ) * Real.pi * t : ℝ) : ℂ))
  have hpath :
      Complex.finiteAbelPlanaCotangentKernel (Complex.I * (t : ℂ)) +
          (Real.pi : ℂ) * Complex.I =
        Complex.finiteAbelPlanaCotangentKernel ((t : ℂ) * Complex.I) +
          (Real.pi : ℂ) * Complex.I := by
    exact congrArg
      (fun z : ℂ =>
        Complex.finiteAbelPlanaCotangentKernel z + (Real.pi : ℂ) * Complex.I)
      (mul_comm Complex.I (t : ℂ))
  exact Eq.trans hpath (Eq.trans hupper hden)

/-- Integer-shifted vertical-axis cotangent exponential denominator
normalization at the right Abel-Plana endpoint. -/
theorem Complex.finiteAbelPlanaCotangentKernel_upper_integerShift_expDenominator
    (M : ℕ)
    (t : ℝ)
    (ht : 0 < t) :
    Complex.finiteAbelPlanaCotangentKernel ((M : ℂ) + Complex.I * (t : ℂ)) +
        (Real.pi : ℂ) * Complex.I =
      -((2 : ℂ) * (Real.pi : ℂ) * Complex.I) /
        (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1) := by
  have hupper :
      Complex.finiteAbelPlanaCotangentKernel (((M : ℝ) : ℂ) + (t : ℂ) * Complex.I) +
          (Real.pi : ℂ) * Complex.I =
        -((2 : ℂ) * (Real.pi : ℂ) * Complex.I) *
          (Complex.finiteAbelPlanaCotangentUpperQ (M : ℝ) t /
            (1 - Complex.finiteAbelPlanaCotangentUpperQ (M : ℝ) t)) :=
    Complex.finiteAbelPlanaCotangentKernel_upper_exp_formula (M : ℝ) t ht
  have hperiod :
      Complex.exp (((M : ℤ) : ℂ) * ((2 : ℂ) * (Real.pi : ℂ) * Complex.I)) = 1 := by
    exact
      Complex.exp_eq_one_iff.mpr
        ⟨(M : ℤ), rfl⟩
  have hden :
      -((2 : ℂ) * (Real.pi : ℂ) * Complex.I) *
          (Complex.finiteAbelPlanaCotangentUpperQ (M : ℝ) t /
        (1 - Complex.finiteAbelPlanaCotangentUpperQ (M : ℝ) t)) =
        -((2 : ℂ) * (Real.pi : ℂ) * Complex.I) /
          (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1) := by
    have hq :
        Complex.finiteAbelPlanaCotangentUpperQ (M : ℝ) t =
          (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ))⁻¹ :=
      Complex.finiteAbelPlanaCotangentUpperQ_intShift_eq_exp_height_inv M t
    calc
      -((2 : ℂ) * (Real.pi : ℂ) * Complex.I) *
          (Complex.finiteAbelPlanaCotangentUpperQ (M : ℝ) t /
        (1 - Complex.finiteAbelPlanaCotangentUpperQ (M : ℝ) t)) =
        -((2 : ℂ) * (Real.pi : ℂ) * Complex.I) *
          ((Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ))⁻¹ /
        (1 - (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ))⁻¹)) := by
        exact congrArg
          (fun q : ℂ =>
            -((2 : ℂ) * (Real.pi : ℂ) * Complex.I) * (q / (1 - q)))
          hq
      _ =
        -((2 : ℂ) * (Real.pi : ℂ) * Complex.I) /
          (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1) :=
        Complex.neg_mul_inv_div_one_sub_inv_eq_neg_div_sub_one
          ((2 : ℂ) * (Real.pi : ℂ) * Complex.I)
          (Complex.exp_ne_zero (((2 : ℝ) * Real.pi * t : ℝ) : ℂ))
  have hpath :
      (((M : ℝ) : ℂ) + (t : ℂ) * Complex.I) =
        (M : ℂ) + Complex.I * (t : ℂ) := by
    exact
      congrArg
        (fun u : ℂ => (M : ℂ) + u)
        (mul_comm (t : ℂ) Complex.I)
  have hpath_transport :
      Complex.finiteAbelPlanaCotangentKernel (((M : ℝ) : ℂ) + (t : ℂ) * Complex.I) +
          (Real.pi : ℂ) * Complex.I =
        Complex.finiteAbelPlanaCotangentKernel ((M : ℂ) + Complex.I * (t : ℂ)) +
          (Real.pi : ℂ) * Complex.I :=
    congrArg
      (fun z : ℂ =>
        Complex.finiteAbelPlanaCotangentKernel z + (Real.pi : ℂ) * Complex.I)
      hpath
  exact Eq.trans hpath_transport.symm (Eq.trans hupper hden)

/-- Vertical-axis lower-half cotangent exponential denominator normalization.

The lower-half-plane cotangent remainder on `-I*t` has the same Abel-Plana
kernel denominator as the upper half-plane remainder. -/
theorem Complex.finiteAbelPlanaCotangentKernel_lower_vertical_expDenominator
    (t : ℝ)
    (ht : 0 < t) :
    Complex.finiteAbelPlanaCotangentKernel (-(Complex.I * (t : ℂ))) -
        (Real.pi : ℂ) * Complex.I =
      (2 : ℂ) * (Real.pi : ℂ) * Complex.I /
        (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1) := by
  have hlower :
      Complex.finiteAbelPlanaCotangentKernel (-((t : ℂ) * Complex.I)) -
          (Real.pi : ℂ) * Complex.I =
        ((2 : ℂ) * (Real.pi : ℂ) * Complex.I) *
          (Complex.finiteAbelPlanaCotangentLowerQ 0 t /
            (1 - Complex.finiteAbelPlanaCotangentLowerQ 0 t)) :=
    Complex.finiteAbelPlanaCotangentKernel_lower_vertical_exp_formula t ht
  have hden :
      ((2 : ℂ) * (Real.pi : ℂ) * Complex.I) *
          (Complex.finiteAbelPlanaCotangentLowerQ 0 t /
            (1 - Complex.finiteAbelPlanaCotangentLowerQ 0 t)) =
        (2 : ℂ) * (Real.pi : ℂ) * Complex.I /
          (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1) := by
    have hq :
        Complex.finiteAbelPlanaCotangentLowerQ 0 t =
          (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ))⁻¹ :=
      Complex.finiteAbelPlanaCotangentLowerQ_zero_eq_exp_height_inv t
    calc
      ((2 : ℂ) * (Real.pi : ℂ) * Complex.I) *
          (Complex.finiteAbelPlanaCotangentLowerQ 0 t /
            (1 - Complex.finiteAbelPlanaCotangentLowerQ 0 t)) =
        ((2 : ℂ) * (Real.pi : ℂ) * Complex.I) *
          ((Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ))⁻¹ /
            (1 - (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ))⁻¹)) := by
        exact congrArg
          (fun q : ℂ =>
            ((2 : ℂ) * (Real.pi : ℂ) * Complex.I) * (q / (1 - q)))
          hq
      _ =
        (2 : ℂ) * (Real.pi : ℂ) * Complex.I /
          (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1) :=
        Complex.mul_inv_div_one_sub_inv_eq_div_sub_one
          ((2 : ℂ) * (Real.pi : ℂ) * Complex.I)
          (Complex.exp_ne_zero (((2 : ℝ) * Real.pi * t : ℝ) : ℂ))
  have hpath :
      (-((t : ℂ) * Complex.I)) = -(Complex.I * (t : ℂ)) := by
    exact congrArg Neg.neg (mul_comm (t : ℂ) Complex.I)
  have hpath_transport :
      Complex.finiteAbelPlanaCotangentKernel (-((t : ℂ) * Complex.I)) -
          (Real.pi : ℂ) * Complex.I =
        Complex.finiteAbelPlanaCotangentKernel (-(Complex.I * (t : ℂ))) -
          (Real.pi : ℂ) * Complex.I :=
    congrArg
      (fun z : ℂ =>
        Complex.finiteAbelPlanaCotangentKernel z - (Real.pi : ℂ) * Complex.I)
      hpath
  exact Eq.trans hpath_transport.symm (Eq.trans hlower hden)

/-- Integer-shifted lower-half cotangent exponential denominator
normalization at the right Abel-Plana endpoint. -/
theorem Complex.finiteAbelPlanaCotangentKernel_lower_integerShift_expDenominator
    (M : ℕ)
    (t : ℝ)
    (ht : 0 < t) :
    Complex.finiteAbelPlanaCotangentKernel ((M : ℂ) - Complex.I * (t : ℂ)) -
        (Real.pi : ℂ) * Complex.I =
      (2 : ℂ) * (Real.pi : ℂ) * Complex.I /
        (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1) := by
  have hlower :
      Complex.finiteAbelPlanaCotangentKernel (((M : ℝ) : ℂ) - (t : ℂ) * Complex.I) -
          (Real.pi : ℂ) * Complex.I =
        ((2 : ℂ) * (Real.pi : ℂ) * Complex.I) *
          (Complex.finiteAbelPlanaCotangentLowerQ (M : ℝ) t /
            (1 - Complex.finiteAbelPlanaCotangentLowerQ (M : ℝ) t)) :=
    Complex.finiteAbelPlanaCotangentKernel_lower_exp_formula (M : ℝ) t ht
  have hperiod :
      Complex.exp (-(((M : ℤ) : ℂ) * ((2 : ℂ) * (Real.pi : ℂ) * Complex.I))) = 1 := by
    have hbase :
        Complex.exp (((M : ℤ) : ℂ) * ((2 : ℂ) * (Real.pi : ℂ) * Complex.I)) = 1 := by
      exact
        Complex.exp_eq_one_iff.mpr
          ⟨(M : ℤ), rfl⟩
    calc
      Complex.exp (-(((M : ℤ) : ℂ) * ((2 : ℂ) * (Real.pi : ℂ) * Complex.I))) =
          (Complex.exp (((M : ℤ) : ℂ) * ((2 : ℂ) * (Real.pi : ℂ) * Complex.I)))⁻¹ :=
        Complex.exp_neg (((M : ℤ) : ℂ) * ((2 : ℂ) * (Real.pi : ℂ) * Complex.I))
      _ = 1⁻¹ := congrArg Inv.inv hbase
      _ = 1 := inv_one
  have hden :
      ((2 : ℂ) * (Real.pi : ℂ) * Complex.I) *
          (Complex.finiteAbelPlanaCotangentLowerQ (M : ℝ) t /
            (1 - Complex.finiteAbelPlanaCotangentLowerQ (M : ℝ) t)) =
        (2 : ℂ) * (Real.pi : ℂ) * Complex.I /
          (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1) := by
    have hq :
        Complex.finiteAbelPlanaCotangentLowerQ (M : ℝ) t =
          (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ))⁻¹ :=
      Complex.finiteAbelPlanaCotangentLowerQ_intShift_eq_exp_height_inv M t
    calc
      ((2 : ℂ) * (Real.pi : ℂ) * Complex.I) *
          (Complex.finiteAbelPlanaCotangentLowerQ (M : ℝ) t /
            (1 - Complex.finiteAbelPlanaCotangentLowerQ (M : ℝ) t)) =
        ((2 : ℂ) * (Real.pi : ℂ) * Complex.I) *
          ((Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ))⁻¹ /
            (1 - (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ))⁻¹)) := by
        exact congrArg
          (fun q : ℂ =>
            ((2 : ℂ) * (Real.pi : ℂ) * Complex.I) * (q / (1 - q)))
          hq
      _ =
        (2 : ℂ) * (Real.pi : ℂ) * Complex.I /
          (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1) :=
        Complex.mul_inv_div_one_sub_inv_eq_div_sub_one
          ((2 : ℂ) * (Real.pi : ℂ) * Complex.I)
          (Complex.exp_ne_zero (((2 : ℝ) * Real.pi * t : ℝ) : ℂ))
  have hpath :
      (((M : ℝ) : ℂ) - (t : ℂ) * Complex.I) =
        (M : ℂ) - Complex.I * (t : ℂ) := by
    exact
      congrArg
        (fun u : ℂ => (M : ℂ) - u)
        (mul_comm (t : ℂ) Complex.I)
  have hpath_transport :
      Complex.finiteAbelPlanaCotangentKernel (((M : ℝ) : ℂ) - (t : ℂ) * Complex.I) -
          (Real.pi : ℂ) * Complex.I =
        Complex.finiteAbelPlanaCotangentKernel ((M : ℂ) - Complex.I * (t : ℂ)) -
          (Real.pi : ℂ) * Complex.I :=
    congrArg
      (fun z : ℂ =>
        Complex.finiteAbelPlanaCotangentKernel z - (Real.pi : ℂ) * Complex.I)
      hpath
  exact Eq.trans hpath_transport.symm (Eq.trans hlower hden)

/-- Negative-half change of variables for the left vertical exponential
remainder.

This is the `y = -t` substitution on the lower half-line piece of the PV
left vertical remainder. -/
theorem Complex.finiteAbelPlana_log_leftVerticalRemainderPV_negativeHalf_changeVariables
    (w : ℂ)
    (T ε : ℝ)
    (hε : 0 < ε)
    (hεT : ε < T) :
    (-Complex.I) *
        (∫ y : ℝ in (-T)..(-ε),
          Complex.finiteAbelPlanaLogSummand w (Complex.I * (y : ℂ)) *
            (Complex.finiteAbelPlanaCotangentKernel (Complex.I * (y : ℂ)) -
              (Real.pi : ℂ) * Complex.I)) =
      (-Complex.I) *
        (∫ t : ℝ in ε..T,
          Complex.finiteAbelPlanaLogSummand w (-(Complex.I * (t : ℂ))) *
            (Complex.finiteAbelPlanaCotangentKernel (-(Complex.I * (t : ℂ))) -
              (Real.pi : ℂ) * Complex.I)) := by
  let F : ℝ → ℂ :=
    fun y =>
      Complex.finiteAbelPlanaLogSummand w (Complex.I * (y : ℂ)) *
        (Complex.finiteAbelPlanaCotangentKernel (Complex.I * (y : ℂ)) -
          (Real.pi : ℂ) * Complex.I)
  have hsub :
      (∫ t : ℝ in ε..T, F (-t)) =
        ∫ y : ℝ in (-T)..(-ε), F y :=
    intervalIntegral.integral_comp_neg (f := F) (a := ε) (b := T)
  have hpoint :
    ∀ t : ℝ,
        F (-t) =
          Complex.finiteAbelPlanaLogSummand w (-(Complex.I * (t : ℂ))) *
            (Complex.finiteAbelPlanaCotangentKernel (-(Complex.I * (t : ℂ))) -
              (Real.pi : ℂ) * Complex.I) := by
    intro t
    unfold F
    exact congrArg₂ HMul.hMul
      (congrArg
        (fun u : ℂ => Complex.finiteAbelPlanaLogSummand w u)
        (Complex.I_mul_neg_real_eq_neg_I_mul t))
      (congrArg
        (fun u : ℂ =>
          Complex.finiteAbelPlanaCotangentKernel u -
            (Real.pi : ℂ) * Complex.I)
        (Complex.I_mul_neg_real_eq_neg_I_mul t))
  have hintegral :
      (∫ y : ℝ in (-T)..(-ε), F y) =
        ∫ t : ℝ in ε..T,
          Complex.finiteAbelPlanaLogSummand w (-(Complex.I * (t : ℂ))) *
            (Complex.finiteAbelPlanaCotangentKernel (-(Complex.I * (t : ℂ))) -
              (Real.pi : ℂ) * Complex.I) := by
    exact Eq.trans hsub.symm
      (intervalIntegral.integral_congr (fun t _ht => hpoint t))
  exact congrArg (fun z : ℂ => (-Complex.I) * z) hintegral

/-- Positive-half cotangent exponential formula for the left vertical
exponential remainder. -/
theorem Complex.finiteAbelPlana_log_leftVerticalRemainderPV_positiveHalf_expFormula
    (w : ℂ)
    (t : ℝ)
    (ht : 0 < t) :
    (-Complex.I) *
        (Complex.finiteAbelPlanaLogSummand w (Complex.I * (t : ℂ)) *
          (Complex.finiteAbelPlanaCotangentKernel (Complex.I * (t : ℂ)) +
            (Real.pi : ℂ) * Complex.I)) =
      (-Complex.I) *
        (Complex.finiteAbelPlanaLogSummand w (Complex.I * (t : ℂ)) *
          (-((2 : ℂ) * (Real.pi : ℂ) * Complex.I) /
            (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1))) := by
  have hkernel :
      Complex.finiteAbelPlanaCotangentKernel (Complex.I * (t : ℂ)) +
          (Real.pi : ℂ) * Complex.I =
        -((2 : ℂ) * (Real.pi : ℂ) * Complex.I) /
          (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1) :=
    Complex.finiteAbelPlanaCotangentKernel_upper_vertical_expDenominator t ht
  exact
    congrArg
      (fun z : ℂ =>
        (-Complex.I) *
          (Complex.finiteAbelPlanaLogSummand w (Complex.I * (t : ℂ)) * z))
      hkernel

/-- Pointwise normalized left vertical exponential-remainder jump.

After residue normalization by `(2πi)⁻¹`, the lower and upper half-plane
cotangent remainders assemble into the lower Abel-Plana logarithmic jump
integrand. -/
theorem Complex.finiteAbelPlana_log_leftVerticalRemainderPV_pointwise_normalizedJump
    (w : ℂ)
    (t : ℝ)
    (ht : 0 < t) :
    ((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹ *
      (((-Complex.I) *
          (Complex.finiteAbelPlanaLogSummand w (-(Complex.I * (t : ℂ))) *
            (Complex.finiteAbelPlanaCotangentKernel (-(Complex.I * (t : ℂ))) -
              (Real.pi : ℂ) * Complex.I))) +
        ((-Complex.I) *
          (Complex.finiteAbelPlanaLogSummand w (Complex.I * (t : ℂ)) *
            (Complex.finiteAbelPlanaCotangentKernel (Complex.I * (t : ℂ)) +
              (Real.pi : ℂ) * Complex.I)))) =
      -Complex.finiteAbelPlanaLogLowerVerticalIntegrand w t := by
  have hlower :
      Complex.finiteAbelPlanaCotangentKernel (-(Complex.I * (t : ℂ))) -
          (Real.pi : ℂ) * Complex.I =
        (2 : ℂ) * (Real.pi : ℂ) * Complex.I /
          (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1) :=
    Complex.finiteAbelPlanaCotangentKernel_lower_vertical_expDenominator t ht
  have hupper :
      Complex.finiteAbelPlanaCotangentKernel (Complex.I * (t : ℂ)) +
          (Real.pi : ℂ) * Complex.I =
        -((2 : ℂ) * (Real.pi : ℂ) * Complex.I) /
          (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1) :=
    Complex.finiteAbelPlanaCotangentKernel_upper_vertical_expDenominator t ht
  have hden_ne :
      Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1 ≠ 0 := by
    exact Complex.exp_two_pi_real_sub_one_ne_zero ht
  have htwo_pi_I_ne : ((2 : ℂ) * (Real.pi : ℂ) * Complex.I) ≠ 0 := by
    exact Complex.two_pi_I_ne_zero
  unfold Complex.finiteAbelPlanaLogSummand
    Complex.finiteAbelPlanaLogLowerVerticalIntegrand
  have hsubstitution :
      ((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹ *
        (((-Complex.I) *
            (Complex.log (w - Complex.I * (t : ℂ)) *
              ((2 : ℂ) * (Real.pi : ℂ) * Complex.I /
                (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1)))) +
          ((-Complex.I) *
            (Complex.log (w + Complex.I * (t : ℂ)) *
              (-((2 : ℂ) * (Real.pi : ℂ) * Complex.I) /
                (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1))))) =
        -((-Complex.I) *
          ((Complex.log (w + Complex.I * (t : ℂ)) -
              Complex.log (w - Complex.I * (t : ℂ))) /
            (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1))) :=
    Complex.normalized_twoHalf_logJump_algebra
      htwo_pi_I_ne
      (-Complex.I)
      (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1)
      (Complex.log (w + Complex.I * (t : ℂ)))
      (Complex.log (w - Complex.I * (t : ℂ)))
  have hraw :
      ((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹ *
        (((-Complex.I) *
            (Complex.log (w - Complex.I * (t : ℂ)) *
              (Complex.finiteAbelPlanaCotangentKernel (-(Complex.I * (t : ℂ))) -
                (Real.pi : ℂ) * Complex.I))) +
          ((-Complex.I) *
            (Complex.log (w + Complex.I * (t : ℂ)) *
              (Complex.finiteAbelPlanaCotangentKernel (Complex.I * (t : ℂ)) +
                (Real.pi : ℂ) * Complex.I)))) =
        -((-Complex.I) *
          ((Complex.log (w + Complex.I * (t : ℂ)) -
              Complex.log (w - Complex.I * (t : ℂ))) /
            (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1))) :=
    Eq.trans
      (congrArg₂
      (fun lower upper : ℂ =>
        ((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹ *
          (((-Complex.I) *
              (Complex.log (w - Complex.I * (t : ℂ)) * lower)) +
            ((-Complex.I) *
              (Complex.log (w + Complex.I * (t : ℂ)) * upper))))
      hlower hupper)
      hsubstitution
  have htarget :
      -((-Complex.I) *
          ((Complex.log (w + Complex.I * (t : ℂ)) -
              Complex.log (w - Complex.I * (t : ℂ))) /
            (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1))) =
        -((-Complex.I) *
          ((Complex.log (w + (t : ℂ) * Complex.I) -
              Complex.log (w - (t : ℂ) * Complex.I)) /
            (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1))) := by
    have hplus :
        w + Complex.I * (t : ℂ) = w + (t : ℂ) * Complex.I :=
      congrArg (fun z : ℂ => w + z) (mul_comm Complex.I (t : ℂ))
    have hminus :
        w - Complex.I * (t : ℂ) = w - (t : ℂ) * Complex.I :=
      congrArg (fun z : ℂ => w - z) (mul_comm Complex.I (t : ℂ))
    exact congrArg
      (fun z : ℂ =>
        -((-Complex.I) *
          (z / (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1))))
      (congrArg₂ HSub.hSub (congrArg Complex.log hplus) (congrArg Complex.log hminus))
  exact Eq.trans hraw htarget

/-- The two left vertical exponential pieces identify with the named lower
logarithmic-jump integrand on `(ε,T]`. -/
theorem Complex.finiteAbelPlana_log_leftVerticalRemainderPV_cutoffIntegrand_identification
    (w : ℂ)
    (T ε : ℝ)
    (hε : 0 < ε)
    (hεT : ε < T) :
    Complex.finiteAbelPlanaLogLeftVerticalCotangentRemainderSidePVNormalized w T ε =
      -Complex.finiteAbelPlanaLogLowerVerticalIntegralFromTo w ε T := by
  unfold Complex.finiteAbelPlanaLogLeftVerticalCotangentRemainderSidePVNormalized
    Complex.finiteAbelPlanaLogLowerVerticalIntegralFromTo
  calc
    ∫ t : ℝ in Set.Ioc ε T,
      ((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹ *
        (((-Complex.I) *
            (Complex.finiteAbelPlanaLogSummand w (-(Complex.I * (t : ℂ))) *
              (Complex.finiteAbelPlanaCotangentKernel (-(Complex.I * (t : ℂ))) -
                (Real.pi : ℂ) * Complex.I))) +
          ((-Complex.I) *
            (Complex.finiteAbelPlanaLogSummand w (Complex.I * (t : ℂ)) *
              (Complex.finiteAbelPlanaCotangentKernel (Complex.I * (t : ℂ)) +
                (Real.pi : ℂ) * Complex.I)))) =
        ∫ t : ℝ in Set.Ioc ε T,
          -Complex.finiteAbelPlanaLogLowerVerticalIntegrand w t := by
      exact
        setIntegral_congr_fun measurableSet_Ioc
          (fun t ht =>
            Complex.finiteAbelPlana_log_leftVerticalRemainderPV_pointwise_normalizedJump
              w t (lt_trans hε ht.1))
    _ = -∫ t : ℝ in Set.Ioc ε T,
          Complex.finiteAbelPlanaLogLowerVerticalIntegrand w t := by
      exact integral_neg
        (fun t : ℝ => Complex.finiteAbelPlanaLogLowerVerticalIntegrand w t)

/-- Negative-half change of variables for the right endpoint vertical
exponential remainder.

This is the `y = -t` substitution on the lower half-line piece at
`M = N + 1`. -/
theorem Complex.finiteAbelPlana_log_rightVerticalRemainderPV_negativeHalf_changeVariables
    (N : ℕ)
    (w : ℂ)
    (T ε : ℝ)
    (hε : 0 < ε)
    (hεT : ε < T) :
    let M : ℕ := N + 1
    Complex.I *
        (∫ y : ℝ in (-T)..(-ε),
          Complex.finiteAbelPlanaLogSummand w ((M : ℂ) + Complex.I * (y : ℂ)) *
            (Complex.finiteAbelPlanaCotangentKernel ((M : ℂ) + Complex.I * (y : ℂ)) -
              (Real.pi : ℂ) * Complex.I)) =
      Complex.I *
        (∫ t : ℝ in ε..T,
          Complex.finiteAbelPlanaLogSummand w ((M : ℂ) - Complex.I * (t : ℂ)) *
            (Complex.finiteAbelPlanaCotangentKernel ((M : ℂ) - Complex.I * (t : ℂ)) -
              (Real.pi : ℂ) * Complex.I)) := by
  let M : ℕ := N + 1
  let F : ℝ → ℂ :=
    fun y =>
      Complex.finiteAbelPlanaLogSummand w ((M : ℂ) + Complex.I * (y : ℂ)) *
        (Complex.finiteAbelPlanaCotangentKernel ((M : ℂ) + Complex.I * (y : ℂ)) -
          (Real.pi : ℂ) * Complex.I)
  have hsub :
      (∫ t : ℝ in ε..T, F (-t)) =
        ∫ y : ℝ in (-T)..(-ε), F y :=
    intervalIntegral.integral_comp_neg (f := F) (a := ε) (b := T)
  have hpoint :
    ∀ t : ℝ,
        F (-t) =
          Complex.finiteAbelPlanaLogSummand w ((M : ℂ) - Complex.I * (t : ℂ)) *
            (Complex.finiteAbelPlanaCotangentKernel ((M : ℂ) - Complex.I * (t : ℂ)) -
              (Real.pi : ℂ) * Complex.I) := by
    intro t
    unfold F
    exact congrArg₂ HMul.hMul
      (congrArg
        (fun u : ℂ => Complex.finiteAbelPlanaLogSummand w u)
        (Complex.rightVertical_add_I_mul_neg_real_eq_sub_I_mul M t))
      (congrArg
        (fun u : ℂ =>
          Complex.finiteAbelPlanaCotangentKernel u -
            (Real.pi : ℂ) * Complex.I)
        (Complex.rightVertical_add_I_mul_neg_real_eq_sub_I_mul M t))
  have hintegral :
      (∫ y : ℝ in (-T)..(-ε), F y) =
        ∫ t : ℝ in ε..T,
          Complex.finiteAbelPlanaLogSummand w ((M : ℂ) - Complex.I * (t : ℂ)) *
            (Complex.finiteAbelPlanaCotangentKernel ((M : ℂ) - Complex.I * (t : ℂ)) -
              (Real.pi : ℂ) * Complex.I) := by
    exact Eq.trans hsub.symm
      (intervalIntegral.integral_congr (fun t _ht => hpoint t))
  exact congrArg (fun z : ℂ => Complex.I * z) hintegral

/-- Positive-half cotangent exponential formula for the right endpoint
vertical exponential remainder. -/
theorem Complex.finiteAbelPlana_log_rightVerticalRemainderPV_positiveHalf_expFormula
    (N : ℕ)
    (w : ℂ)
    (t : ℝ)
    (ht : 0 < t) :
    let M : ℕ := N + 1
    Complex.I *
        (Complex.finiteAbelPlanaLogSummand w ((M : ℂ) + Complex.I * (t : ℂ)) *
          (Complex.finiteAbelPlanaCotangentKernel ((M : ℂ) + Complex.I * (t : ℂ)) +
            (Real.pi : ℂ) * Complex.I)) =
      Complex.I *
        (Complex.finiteAbelPlanaLogSummand w ((M : ℂ) + Complex.I * (t : ℂ)) *
          (-((2 : ℂ) * (Real.pi : ℂ) * Complex.I) /
            (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1))) := by
  let M : ℕ := N + 1
  have hkernel :
      Complex.finiteAbelPlanaCotangentKernel ((M : ℂ) + Complex.I * (t : ℂ)) +
          (Real.pi : ℂ) * Complex.I =
        -((2 : ℂ) * (Real.pi : ℂ) * Complex.I) /
          (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1) := by
    exact
      Complex.finiteAbelPlanaCotangentKernel_upper_integerShift_expDenominator
        M t ht
  exact
    congrArg
      (fun z : ℂ =>
        Complex.I *
          (Complex.finiteAbelPlanaLogSummand w
            ((M : ℂ) + Complex.I * (t : ℂ)) * z))
      hkernel

/-- Explicit pointwise normalized right endpoint vertical exponential-remainder
jump before folding it into the named upper vertical integrand.  Keeping the
target unfolded prevents the public wrapper from elaborating the endpoint
integrand definition through the full algebraic normalization. -/
theorem Complex.finiteAbelPlana_log_rightVerticalRemainderPV_pointwise_normalizedJump_explicit
    (N : ℕ)
    (w : ℂ)
    (t : ℝ)
    (ht : 0 < t) :
    ((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹ *
      ((Complex.I *
          (Complex.finiteAbelPlanaLogSummand w
            (((N + 1 : ℕ) : ℂ) - Complex.I * (t : ℂ)) *
            (Complex.finiteAbelPlanaCotangentKernel
                (((N + 1 : ℕ) : ℂ) - Complex.I * (t : ℂ)) -
              (Real.pi : ℂ) * Complex.I))) +
        (Complex.I *
          (Complex.finiteAbelPlanaLogSummand w
            (((N + 1 : ℕ) : ℂ) + Complex.I * (t : ℂ)) *
            (Complex.finiteAbelPlanaCotangentKernel
                (((N + 1 : ℕ) : ℂ) + Complex.I * (t : ℂ)) +
              (Real.pi : ℂ) * Complex.I)))) =
      -(Complex.I *
        ((Complex.log
              (w + (((N + 1 : ℕ) : ℂ) + (t : ℂ) * Complex.I)) -
            Complex.log
              (w + (((N + 1 : ℕ) : ℂ) - (t : ℂ) * Complex.I))) /
          (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1))) := by
  have hlower :
      Complex.finiteAbelPlanaCotangentKernel (((N + 1 : ℕ) : ℂ) - Complex.I * (t : ℂ)) -
          (Real.pi : ℂ) * Complex.I =
        (2 : ℂ) * (Real.pi : ℂ) * Complex.I /
          (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1) :=
    Complex.finiteAbelPlanaCotangentKernel_lower_integerShift_expDenominator
      (N + 1) t ht
  have hupper :
      Complex.finiteAbelPlanaCotangentKernel (((N + 1 : ℕ) : ℂ) + Complex.I * (t : ℂ)) +
          (Real.pi : ℂ) * Complex.I =
        -((2 : ℂ) * (Real.pi : ℂ) * Complex.I) /
          (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1) :=
    Complex.finiteAbelPlanaCotangentKernel_upper_integerShift_expDenominator
      (N + 1) t ht
  have htwo_pi_I_ne : ((2 : ℂ) * (Real.pi : ℂ) * Complex.I) ≠ 0 := by
    exact Complex.two_pi_I_ne_zero
  unfold Complex.finiteAbelPlanaLogSummand
  have hsubstitution :
      ((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹ *
        ((Complex.I *
            (Complex.log (w + (((N + 1 : ℕ) : ℂ) - Complex.I * (t : ℂ))) *
              ((2 : ℂ) * (Real.pi : ℂ) * Complex.I /
                (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1)))) +
          (Complex.I *
            (Complex.log (w + (((N + 1 : ℕ) : ℂ) + Complex.I * (t : ℂ))) *
              (-((2 : ℂ) * (Real.pi : ℂ) * Complex.I) /
                (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1))))) =
        -(Complex.I *
          ((Complex.log (w + (((N + 1 : ℕ) : ℂ) + Complex.I * (t : ℂ))) -
              Complex.log (w + (((N + 1 : ℕ) : ℂ) - Complex.I * (t : ℂ)))) /
            (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1))) :=
    Complex.normalized_twoHalf_logJump_algebra
      htwo_pi_I_ne
      Complex.I
      (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1)
      (Complex.log (w + (((N + 1 : ℕ) : ℂ) + Complex.I * (t : ℂ))))
      (Complex.log (w + (((N + 1 : ℕ) : ℂ) - Complex.I * (t : ℂ))))
  have hraw :
      ((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹ *
        ((Complex.I *
            (Complex.log (w + (((N + 1 : ℕ) : ℂ) - Complex.I * (t : ℂ))) *
              (Complex.finiteAbelPlanaCotangentKernel (((N + 1 : ℕ) : ℂ) - Complex.I * (t : ℂ)) -
                (Real.pi : ℂ) * Complex.I))) +
          (Complex.I *
            (Complex.log (w + (((N + 1 : ℕ) : ℂ) + Complex.I * (t : ℂ))) *
              (Complex.finiteAbelPlanaCotangentKernel (((N + 1 : ℕ) : ℂ) + Complex.I * (t : ℂ)) +
                (Real.pi : ℂ) * Complex.I)))) =
        -(Complex.I *
          ((Complex.log (w + (((N + 1 : ℕ) : ℂ) + Complex.I * (t : ℂ))) -
              Complex.log (w + (((N + 1 : ℕ) : ℂ) - Complex.I * (t : ℂ)))) /
            (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1))) :=
    Eq.trans
      (congrArg₂
        (fun lower upper : ℂ =>
          ((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹ *
            ((Complex.I *
                (Complex.log (w + (((N + 1 : ℕ) : ℂ) - Complex.I * (t : ℂ))) * lower)) +
              (Complex.I *
                (Complex.log (w + (((N + 1 : ℕ) : ℂ) + Complex.I * (t : ℂ))) * upper))))
        hlower hupper)
      hsubstitution
  have htarget :
      -(Complex.I *
          ((Complex.log (w + (((N + 1 : ℕ) : ℂ) + Complex.I * (t : ℂ))) -
              Complex.log (w + (((N + 1 : ℕ) : ℂ) - Complex.I * (t : ℂ)))) /
            (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1))) =
        -(Complex.I *
          ((Complex.log
                (w + (((N + 1 : ℕ) : ℂ) + (t : ℂ) * Complex.I)) -
              Complex.log
                (w + (((N + 1 : ℕ) : ℂ) - (t : ℂ) * Complex.I))) /
            (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1))) := by
    have hplus :
        w + (((N + 1 : ℕ) : ℂ) + Complex.I * (t : ℂ)) =
          w + (((N + 1 : ℕ) : ℂ) + (t : ℂ) * Complex.I) := by
      exact congrArg (fun z : ℂ => w + (((N + 1 : ℕ) : ℂ) + z))
        (mul_comm Complex.I (t : ℂ))
    have hminus :
        w + (((N + 1 : ℕ) : ℂ) - Complex.I * (t : ℂ)) =
          w + (((N + 1 : ℕ) : ℂ) - (t : ℂ) * Complex.I) := by
      exact congrArg (fun z : ℂ => w + (((N + 1 : ℕ) : ℂ) - z))
        (mul_comm Complex.I (t : ℂ))
    exact congrArg
      (fun z : ℂ =>
        -(Complex.I *
          (z / (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1))))
      (congrArg₂ HSub.hSub (congrArg Complex.log hplus) (congrArg Complex.log hminus))
  exact Eq.trans hraw htarget

/-- Pointwise normalized right endpoint vertical exponential-remainder jump.

This is the endpoint-shifted analogue of
`finiteAbelPlana_log_leftVerticalRemainderPV_pointwise_normalizedJump`. -/
theorem Complex.finiteAbelPlana_log_rightVerticalRemainderPV_pointwise_normalizedJump
    (N : ℕ)
    (w : ℂ)
    (t : ℝ)
    (ht : 0 < t) :
    ((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹ *
      ((Complex.I *
          (Complex.finiteAbelPlanaLogSummand w
            (((N + 1 : ℕ) : ℂ) - Complex.I * (t : ℂ)) *
            (Complex.finiteAbelPlanaCotangentKernel
                (((N + 1 : ℕ) : ℂ) - Complex.I * (t : ℂ)) -
              (Real.pi : ℂ) * Complex.I))) +
        (Complex.I *
          (Complex.finiteAbelPlanaLogSummand w
            (((N + 1 : ℕ) : ℂ) + Complex.I * (t : ℂ)) *
            (Complex.finiteAbelPlanaCotangentKernel
                (((N + 1 : ℕ) : ℂ) + Complex.I * (t : ℂ)) +
              (Real.pi : ℂ) * Complex.I)))) =
      -Complex.finiteAbelPlanaLogUpperVerticalIntegrand N w t := by
  have hexplicit :=
    Complex.finiteAbelPlana_log_rightVerticalRemainderPV_pointwise_normalizedJump_explicit
      N w t ht
  have hfold :
      -(Complex.I *
        ((Complex.log
              (w + (((N + 1 : ℕ) : ℂ) + (t : ℂ) * Complex.I)) -
            Complex.log
              (w + (((N + 1 : ℕ) : ℂ) - (t : ℂ) * Complex.I))) /
          (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1))) =
      -Complex.finiteAbelPlanaLogUpperVerticalIntegrand N w t := by
    unfold Complex.finiteAbelPlanaLogUpperVerticalIntegrand
      Complex.binetAbelPlanaFiniteUpperLogJump
    have hplus :
        w + (((N + 1 : ℕ) : ℂ) + (t : ℂ) * Complex.I) =
          w + ((N + 1 : ℕ) : ℂ) + (t : ℂ) * Complex.I := by
      exact (add_assoc w (((N + 1 : ℕ) : ℂ)) ((t : ℂ) * Complex.I)).symm
    have hminus :
        w + (((N + 1 : ℕ) : ℂ) - (t : ℂ) * Complex.I) =
          w + ((N + 1 : ℕ) : ℂ) - (t : ℂ) * Complex.I := by
      exact Eq.trans
        (congrArg (fun z : ℂ => w + z)
          (sub_eq_add_neg (((N + 1 : ℕ) : ℂ)) ((t : ℂ) * Complex.I)))
        (Eq.trans
          (Eq.symm
            (add_assoc w (((N + 1 : ℕ) : ℂ)) (-((t : ℂ) * Complex.I))))
          (Eq.symm
            (sub_eq_add_neg (w + ((N + 1 : ℕ) : ℂ)) ((t : ℂ) * Complex.I))))
    exact congrArg
      (fun z : ℂ =>
        -(Complex.I *
          (z / (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1))))
      (congrArg₂ HSub.hSub (congrArg Complex.log hplus) (congrArg Complex.log hminus))
  exact Eq.trans hexplicit hfold

/-- The two right endpoint vertical exponential pieces identify with the named
upper logarithmic-jump integrand on `(ε,T]`. -/
theorem Complex.finiteAbelPlana_log_rightVerticalRemainderPV_cutoffIntegrand_identification
    (N : ℕ)
    (w : ℂ)
    (T ε : ℝ)
    (hε : 0 < ε)
    (hεT : ε < T) :
    Complex.finiteAbelPlanaLogRightVerticalCotangentRemainderSidePVNormalized N w T ε =
      -Complex.finiteAbelPlanaLogUpperVerticalIntegralFromTo N w ε T := by
  unfold Complex.finiteAbelPlanaLogRightVerticalCotangentRemainderSidePVNormalized
    Complex.finiteAbelPlanaLogUpperVerticalIntegralFromTo
  have hpoint :
      (let M : ℕ := N + 1;
        ∫ t : ℝ in Set.Ioc ε T,
          ((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹ *
            ((Complex.I *
                (Complex.finiteAbelPlanaLogSummand w ((M : ℂ) - Complex.I * (t : ℂ)) *
                  (Complex.finiteAbelPlanaCotangentKernel ((M : ℂ) - Complex.I * (t : ℂ)) -
                    (Real.pi : ℂ) * Complex.I))) +
              (Complex.I *
                (Complex.finiteAbelPlanaLogSummand w ((M : ℂ) + Complex.I * (t : ℂ)) *
                  (Complex.finiteAbelPlanaCotangentKernel ((M : ℂ) + Complex.I * (t : ℂ)) +
                    (Real.pi : ℂ) * Complex.I))))) =
        ∫ t : ℝ in Set.Ioc ε T,
          -Complex.finiteAbelPlanaLogUpperVerticalIntegrand N w t := by
    exact setIntegral_congr_fun measurableSet_Ioc
      (fun t ht =>
        Complex.finiteAbelPlana_log_rightVerticalRemainderPV_pointwise_normalizedJump
          N w t (lt_trans hε ht.1))
  exact Eq.trans hpoint
    (integral_neg
      (fun t : ℝ => Complex.finiteAbelPlanaLogUpperVerticalIntegrand N w t))

/-- Left exponential-remainder PV side equals the cutoff lower vertical
logarithmic-jump integral. -/
theorem Complex.finiteAbelPlana_log_leftVerticalRemainderPV_eq_cutoffLowerVertical
    (w : ℂ)
    (T ε : ℝ)
    (hε : 0 < ε)
    (hεT : ε < T) :
    Complex.finiteAbelPlanaLogLeftVerticalCotangentRemainderSidePVNormalized w T ε =
      -Complex.finiteAbelPlanaLogLowerVerticalIntegralFromTo w ε T := by
  exact
    Complex.finiteAbelPlana_log_leftVerticalRemainderPV_cutoffIntegrand_identification
      w T ε hε hεT

/-- Right exponential-remainder PV side equals the cutoff upper vertical
endpoint logarithmic-jump integral. -/
theorem Complex.finiteAbelPlana_log_rightVerticalRemainderPV_eq_cutoffUpperVertical
    (N : ℕ)
    (w : ℂ)
    (T ε : ℝ)
    (hε : 0 < ε)
    (hεT : ε < T) :
    Complex.finiteAbelPlanaLogRightVerticalCotangentRemainderSidePVNormalized N w T ε =
      -Complex.finiteAbelPlanaLogUpperVerticalIntegralFromTo N w ε T := by
  exact
    Complex.finiteAbelPlana_log_rightVerticalRemainderPV_cutoffIntegrand_identification
      N w T ε hε hεT

/-- Cutoff lower vertical integrals converge to the finite window as the lower
cutoff tends to zero from the right. -/
theorem Complex.finiteAbelPlana_log_lowerVerticalIntegralFromTo_tendsto_upTo
    {w : ℂ}
    (hw : 0 < w.re)
    (T : ℝ)
    (hT : 0 < T) :
    Tendsto
      (fun ε : ℝ =>
        Complex.finiteAbelPlanaLogLowerVerticalIntegralFromTo w ε T)
      (𝓝[>] (0 : ℝ))
      (𝓝 (Complex.finiteAbelPlanaLogLowerVerticalIntegralUpTo w T)) := by
  have hIoi :
      IntegrableOn
        (fun t : ℝ => Complex.finiteAbelPlanaLogLowerVerticalIntegrand w t)
        (Set.Ioi (0 : ℝ)) :=
    Complex.finiteAbelPlana_log_lowerVerticalIntegrand_integrableOn_Ioi hw
  have hIoc :
      IntegrableOn
        (fun t : ℝ => Complex.finiteAbelPlanaLogLowerVerticalIntegrand w t)
        (Set.Ioc (0 : ℝ) T) :=
    hIoi.mono_set (fun t ht => ht.1)
  exact
    Complex.tendsto_integral_Ioc_lower_cutoff_real_of_integrableOn_Ioc
      hIoc hT

/-- Cutoff upper vertical integrals converge to the finite window as the lower
cutoff tends to zero from the right. -/
theorem Complex.finiteAbelPlana_log_upperVerticalIntegralFromTo_tendsto_upTo
    (N : ℕ)
    {w : ℂ}
    (hw : 0 < w.re)
    (T : ℝ)
    (hT : 0 < T) :
    Tendsto
      (fun ε : ℝ =>
        Complex.finiteAbelPlanaLogUpperVerticalIntegralFromTo N w ε T)
      (𝓝[>] (0 : ℝ))
      (𝓝 (Complex.finiteAbelPlanaLogUpperVerticalIntegralUpTo N w T)) := by
  have hIoi :
      IntegrableOn
        (fun t : ℝ => Complex.finiteAbelPlanaLogUpperVerticalIntegrand N w t)
        (Set.Ioi (0 : ℝ)) :=
    Complex.finiteAbelPlana_log_upperVerticalIntegrand_integrableOn_Ioi
      hw N
  have hIoc :
      IntegrableOn
        (fun t : ℝ => Complex.finiteAbelPlanaLogUpperVerticalIntegrand N w t)
        (Set.Ioc (0 : ℝ) T) :=
    hIoi.mono_set (fun t ht => ht.1)
  exact
    Complex.tendsto_integral_Ioc_lower_cutoff_real_of_integrableOn_Ioc
      hIoc hT

/-- PV left constant vertical side converges to the ordinary left constant
vertical side as the symmetric indentation radius tends to zero.

This is the local primitive-continuity input for the constant cotangent kernel:
the only missing mass is the slit `(-ε,ε)` around the endpoint indentation, and
its interval integral tends to zero. -/
theorem Complex.finiteAbelPlana_log_leftConstantSidePV_tendsto_constantSide
    {w : ℂ}
    (hw : 0 < w.re)
    (T : ℝ)
    (hT : 0 < T) :
    Tendsto
      (fun ε : ℝ =>
        Complex.finiteAbelPlanaLogLeftVerticalCotangentConstantSidePV w T ε)
      (𝓝[>] (0 : ℝ))
      (𝓝 (Complex.finiteAbelPlanaLogLeftVerticalCotangentConstantSide w T)) := by
  let gLower : ℝ → ℂ := fun y : ℝ =>
    Complex.finiteAbelPlanaLogSummand w (Complex.I * (y : ℂ)) *
      ((Real.pi : ℂ) * Complex.I)
  let gUpper : ℝ → ℂ := fun y : ℝ =>
    Complex.finiteAbelPlanaLogSummand w (Complex.I * (y : ℂ)) *
      (-(Real.pi : ℂ) * Complex.I)
  have harg_neg :
      Tendsto (fun ε : ℝ => -ε) (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) :=
    let hraw :
        Tendsto (fun ε : ℝ => -ε) (𝓝 (0 : ℝ)) (𝓝 (-(0 : ℝ))) :=
      (continuousAt_id.neg).tendsto
    let htarget_filter : 𝓝 (-(0 : ℝ)) = 𝓝 (0 : ℝ) :=
      congrArg (fun x : ℝ => 𝓝 x) (neg_zero : -(0 : ℝ) = 0)
    let hneg_nhds :
        Tendsto (fun ε : ℝ => -ε) (𝓝 (0 : ℝ)) (𝓝 (0 : ℝ)) :=
      htarget_filter ▸ hraw
    tendsto_nhdsWithin_of_tendsto_nhds hneg_nhds
  have hneg_primitive :
      Continuous (fun b : ℝ => ∫ y : ℝ in (-T)..b, gLower y) :=
    intervalIntegral.continuous_primitive
      (fun a b =>
        Complex.intervalIntegrable_finiteAbelPlana_log_leftConstantVerticalIntegrand
              hw a b ((Real.pi : ℂ) * Complex.I))
      (-T)
  have hneg :
      Tendsto
        (fun ε : ℝ => ∫ y : ℝ in (-T)..(-ε), gLower y)
        (𝓝[>] (0 : ℝ))
        (𝓝 (∫ y : ℝ in (-T)..(0 : ℝ), gLower y)) :=
    hneg_primitive.continuousAt.tendsto.comp harg_neg
  have hpos_primitive :
      Continuous (fun a : ℝ => ∫ y : ℝ in T..a, gUpper y) :=
    intervalIntegral.continuous_primitive
      (fun a b =>
        Complex.intervalIntegrable_finiteAbelPlana_log_leftConstantVerticalIntegrand
              hw a b (-(Real.pi : ℂ) * Complex.I))
      T
  have hpos_to_T :
      Tendsto
        (fun ε : ℝ => ∫ y : ℝ in T..ε, gUpper y)
        (𝓝[>] (0 : ℝ))
        (𝓝 (∫ y : ℝ in T..(0 : ℝ), gUpper y)) :=
    hpos_primitive.continuousAt.tendsto.comp nhdsWithin_le_nhds
  have hpos :
      Tendsto
        (fun ε : ℝ => ∫ y : ℝ in ε..T, gUpper y)
        (𝓝[>] (0 : ℝ))
        (𝓝 (∫ y : ℝ in (0 : ℝ)..T, gUpper y)) := by
    have hnegated :
        Tendsto
          (fun ε : ℝ => -∫ y : ℝ in T..ε, gUpper y)
          (𝓝[>] (0 : ℝ))
          (𝓝 (-(∫ y : ℝ in T..(0 : ℝ), gUpper y))) :=
      hpos_to_T.neg
    have htarget :
        -(∫ y : ℝ in T..(0 : ℝ), gUpper y) =
          ∫ y : ℝ in (0 : ℝ)..T, gUpper y := by
      exact (intervalIntegral.integral_symm T (0 : ℝ)).symm
    have heq :
        (fun ε : ℝ => ∫ y : ℝ in ε..T, gUpper y) =
          fun ε : ℝ => -∫ y : ℝ in T..ε, gUpper y := by
      funext ε
      exact intervalIntegral.integral_symm T ε
    exact htarget ▸ (heq ▸ hnegated)
  have hsum :
      Tendsto
        (fun ε : ℝ =>
          (∫ y : ℝ in (-T)..(-ε), gLower y) +
            ∫ y : ℝ in ε..T, gUpper y)
        (𝓝[>] (0 : ℝ))
        (𝓝
          ((∫ y : ℝ in (-T)..(0 : ℝ), gLower y) +
            ∫ y : ℝ in (0 : ℝ)..T, gUpper y)) :=
    hneg.add hpos
  have hsource :
      (fun ε : ℝ =>
        Complex.finiteAbelPlanaLogLeftVerticalCotangentConstantSidePV w T ε) =
      (fun ε : ℝ =>
        (∫ y : ℝ in (-T)..(-ε), gLower y) +
          ∫ y : ℝ in ε..T, gUpper y) := by
    exact funext (fun ε => rfl)
  have htarget :
      Complex.finiteAbelPlanaLogLeftVerticalCotangentConstantSide w T =
        (∫ y : ℝ in (-T)..(0 : ℝ), gLower y) +
          ∫ y : ℝ in (0 : ℝ)..T, gUpper y := by
    rfl
  exact hsource ▸ htarget.symm ▸ hsum

/-- PV right constant vertical side converges to the ordinary right constant
vertical side as the symmetric indentation radius tends to zero.

This is the endpoint-`N+1` analogue of
`finiteAbelPlana_log_leftConstantSidePV_tendsto_constantSide`. -/
theorem Complex.finiteAbelPlana_log_rightConstantSidePV_tendsto_constantSide
    (N : ℕ)
    {w : ℂ}
    (hw : 0 < w.re)
    (T : ℝ)
    (hT : 0 < T) :
    Tendsto
      (fun ε : ℝ =>
        Complex.finiteAbelPlanaLogRightVerticalCotangentConstantSidePV N w T ε)
      (𝓝[>] (0 : ℝ))
      (𝓝 (Complex.finiteAbelPlanaLogRightVerticalCotangentConstantSide N w T)) := by
  let gLower : ℝ → ℂ := fun y : ℝ =>
    Complex.finiteAbelPlanaLogSummand w
        (((N + 1 : ℕ) : ℂ) + Complex.I * (y : ℂ)) *
      ((Real.pi : ℂ) * Complex.I)
  let gUpper : ℝ → ℂ := fun y : ℝ =>
    Complex.finiteAbelPlanaLogSummand w
        (((N + 1 : ℕ) : ℂ) + Complex.I * (y : ℂ)) *
      (-(Real.pi : ℂ) * Complex.I)
  have harg_neg :
      Tendsto (fun ε : ℝ => -ε) (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) :=
    let hraw :
        Tendsto (fun ε : ℝ => -ε) (𝓝 (0 : ℝ)) (𝓝 (-(0 : ℝ))) :=
      (continuousAt_id.neg).tendsto
    let htarget_filter : 𝓝 (-(0 : ℝ)) = 𝓝 (0 : ℝ) :=
      congrArg (fun x : ℝ => 𝓝 x) (neg_zero : -(0 : ℝ) = 0)
    let hneg_nhds :
        Tendsto (fun ε : ℝ => -ε) (𝓝 (0 : ℝ)) (𝓝 (0 : ℝ)) :=
      htarget_filter ▸ hraw
    tendsto_nhdsWithin_of_tendsto_nhds hneg_nhds
  have hneg_primitive :
      Continuous (fun b : ℝ => ∫ y : ℝ in (-T)..b, gLower y) :=
    intervalIntegral.continuous_primitive
      (fun a b =>
        Complex.intervalIntegrable_finiteAbelPlana_log_rightConstantVerticalIntegrand
          N hw a b ((Real.pi : ℂ) * Complex.I))
      (-T)
  have hneg :
      Tendsto
        (fun ε : ℝ => ∫ y : ℝ in (-T)..(-ε), gLower y)
        (𝓝[>] (0 : ℝ))
        (𝓝 (∫ y : ℝ in (-T)..(0 : ℝ), gLower y)) :=
    hneg_primitive.continuousAt.tendsto.comp harg_neg
  have hpos_primitive :
      Continuous (fun a : ℝ => ∫ y : ℝ in T..a, gUpper y) :=
    intervalIntegral.continuous_primitive
      (fun a b =>
        Complex.intervalIntegrable_finiteAbelPlana_log_rightConstantVerticalIntegrand
          N hw a b (-(Real.pi : ℂ) * Complex.I))
      T
  have hpos_to_T :
      Tendsto
        (fun ε : ℝ => ∫ y : ℝ in T..ε, gUpper y)
        (𝓝[>] (0 : ℝ))
        (𝓝 (∫ y : ℝ in T..(0 : ℝ), gUpper y)) :=
    hpos_primitive.continuousAt.tendsto.comp nhdsWithin_le_nhds
  have hpos :
      Tendsto
        (fun ε : ℝ => ∫ y : ℝ in ε..T, gUpper y)
        (𝓝[>] (0 : ℝ))
        (𝓝 (∫ y : ℝ in (0 : ℝ)..T, gUpper y)) := by
    have hnegated :
        Tendsto
          (fun ε : ℝ => -∫ y : ℝ in T..ε, gUpper y)
          (𝓝[>] (0 : ℝ))
          (𝓝 (-(∫ y : ℝ in T..(0 : ℝ), gUpper y))) :=
      hpos_to_T.neg
    have htarget :
        -(∫ y : ℝ in T..(0 : ℝ), gUpper y) =
          ∫ y : ℝ in (0 : ℝ)..T, gUpper y := by
      exact (intervalIntegral.integral_symm T (0 : ℝ)).symm
    have heq :
        (fun ε : ℝ => ∫ y : ℝ in ε..T, gUpper y) =
          fun ε : ℝ => -∫ y : ℝ in T..ε, gUpper y := by
      funext ε
      exact intervalIntegral.integral_symm T ε
    exact htarget ▸ (heq ▸ hnegated)
  have hsum :
      Tendsto
        (fun ε : ℝ =>
          (∫ y : ℝ in (-T)..(-ε), gLower y) +
            ∫ y : ℝ in ε..T, gUpper y)
        (𝓝[>] (0 : ℝ))
        (𝓝
          ((∫ y : ℝ in (-T)..(0 : ℝ), gLower y) +
            ∫ y : ℝ in (0 : ℝ)..T, gUpper y)) :=
    hneg.add hpos
  have hsource :
      (fun ε : ℝ =>
        Complex.finiteAbelPlanaLogRightVerticalCotangentConstantSidePV N w T ε) =
      (fun ε : ℝ =>
        (∫ y : ℝ in (-T)..(-ε), gLower y) +
          ∫ y : ℝ in ε..T, gUpper y) := by
    exact funext (fun ε => rfl)
  have htarget :
      Complex.finiteAbelPlanaLogRightVerticalCotangentConstantSide N w T =
        (∫ y : ℝ in (-T)..(0 : ℝ), gLower y) +
          ∫ y : ℝ in (0 : ℝ)..T, gUpper y := by
    rfl
  exact hsource ▸ htarget.symm ▸ hsum

/-- PV left constant-kernel primitive convergence. -/
theorem Complex.finiteAbelPlana_log_leftConstantKernelPV_tendsto_realEndpoint
    (N : ℕ)
    {w : ℂ}
    (hw : 0 < w.re)
    (T : ℝ)
    (hT : 0 < T) :
    Tendsto
      (fun ε : ℝ =>
        ((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹ *
          (-Complex.finiteAbelPlanaLogUpperHorizontalCotangentConstantSide N w T -
            Complex.I * Complex.finiteAbelPlanaLogLeftVerticalCotangentConstantSidePV w T ε))
      (𝓝[>] (0 : ℝ))
      (𝓝
        (((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹ *
          (-Complex.finiteAbelPlanaLogUpperHorizontalCotangentConstantSide N w T -
            Complex.I * Complex.finiteAbelPlanaLogLeftVerticalCotangentConstantSide w T))) := by
  have hside :
      Tendsto
        (fun ε : ℝ =>
          Complex.finiteAbelPlanaLogLeftVerticalCotangentConstantSidePV w T ε)
        (𝓝[>] (0 : ℝ))
        (𝓝 (Complex.finiteAbelPlanaLogLeftVerticalCotangentConstantSide w T)) :=
    Complex.finiteAbelPlana_log_leftConstantSidePV_tendsto_constantSide
      hw T hT
  have hscaled :
      Tendsto
        (fun ε : ℝ =>
          -Complex.finiteAbelPlanaLogUpperHorizontalCotangentConstantSide N w T -
            Complex.I * Complex.finiteAbelPlanaLogLeftVerticalCotangentConstantSidePV w T ε)
        (𝓝[>] (0 : ℝ))
        (𝓝
          (-Complex.finiteAbelPlanaLogUpperHorizontalCotangentConstantSide N w T -
            Complex.I * Complex.finiteAbelPlanaLogLeftVerticalCotangentConstantSide w T)) :=
    (tendsto_const_nhds.sub ((tendsto_const_nhds.mul hside)))
  exact tendsto_const_nhds.mul hscaled

/-- PV right constant-kernel primitive convergence. -/
theorem Complex.finiteAbelPlana_log_rightConstantKernelPV_tendsto_zero
    (N : ℕ)
    {w : ℂ}
    (hw : 0 < w.re)
    (T : ℝ)
    (hT : 0 < T) :
    Tendsto
      (fun ε : ℝ =>
        ((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹ *
          (Complex.finiteAbelPlanaLogLowerHorizontalCotangentConstantSide N w T +
              Complex.I *
                Complex.finiteAbelPlanaLogRightVerticalCotangentConstantSidePV N w T ε))
      (𝓝[>] (0 : ℝ))
      (𝓝
        (((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹ *
          (Complex.finiteAbelPlanaLogLowerHorizontalCotangentConstantSide N w T +
            Complex.I *
              Complex.finiteAbelPlanaLogRightVerticalCotangentConstantSide N w T))) := by
  have hside :
      Tendsto
        (fun ε : ℝ =>
          Complex.finiteAbelPlanaLogRightVerticalCotangentConstantSidePV N w T ε)
        (𝓝[>] (0 : ℝ))
        (𝓝 (Complex.finiteAbelPlanaLogRightVerticalCotangentConstantSide N w T)) :=
    Complex.finiteAbelPlana_log_rightConstantSidePV_tendsto_constantSide
      N hw T hT
  have hscaled :
      Tendsto
        (fun ε : ℝ =>
          Complex.finiteAbelPlanaLogLowerHorizontalCotangentConstantSide N w T +
            Complex.I *
              Complex.finiteAbelPlanaLogRightVerticalCotangentConstantSidePV N w T ε)
        (𝓝[>] (0 : ℝ))
        (𝓝
          (Complex.finiteAbelPlanaLogLowerHorizontalCotangentConstantSide N w T +
            Complex.I *
              Complex.finiteAbelPlanaLogRightVerticalCotangentConstantSide N w T)) :=
    (tendsto_const_nhds.add (tendsto_const_nhds.mul hside))
  exact tendsto_const_nhds.mul hscaled

/-- PV left exponential-remainder convergence. -/
theorem Complex.finiteAbelPlana_log_leftVerticalRemainderPV_tendsto_lowerVertical
    {w : ℂ}
    (hw : 0 < w.re)
    (T : ℝ)
    (hT : 0 < T) :
    Tendsto
      (fun ε : ℝ =>
        Complex.finiteAbelPlanaLogLeftVerticalCotangentRemainderSidePVNormalized w T ε)
      (𝓝[>] (0 : ℝ))
      (𝓝 (-Complex.finiteAbelPlanaLogLowerVerticalIntegralUpTo w T)) := by
  have hevent :
      ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ),
        Complex.finiteAbelPlanaLogLeftVerticalCotangentRemainderSidePVNormalized w T ε =
          -Complex.finiteAbelPlanaLogLowerVerticalIntegralFromTo w ε T := by
    filter_upwards [Ioo_mem_nhdsWithin_Ioi ⟨le_rfl, hT⟩] with ε hε
    exact
      Complex.finiteAbelPlana_log_leftVerticalRemainderPV_eq_cutoffLowerVertical
        w T ε hε.1 hε.2
  have hlim :
      Tendsto
        (fun ε : ℝ =>
          -Complex.finiteAbelPlanaLogLowerVerticalIntegralFromTo w ε T)
        (𝓝[>] (0 : ℝ))
        (𝓝 (-Complex.finiteAbelPlanaLogLowerVerticalIntegralUpTo w T)) :=
    (Complex.finiteAbelPlana_log_lowerVerticalIntegralFromTo_tendsto_upTo
      hw T hT).neg
  have hevent_symm :
      (fun ε : ℝ =>
          -Complex.finiteAbelPlanaLogLowerVerticalIntegralFromTo w ε T) =ᶠ[𝓝[>] (0 : ℝ)]
        (fun ε : ℝ =>
          Complex.finiteAbelPlanaLogLeftVerticalCotangentRemainderSidePVNormalized w T ε) :=
    hevent.mono (fun ε hε => hε.symm)
  exact hlim.congr' hevent_symm

/-- PV right exponential-remainder convergence. -/
theorem Complex.finiteAbelPlana_log_rightVerticalRemainderPV_tendsto_upperVertical
    (N : ℕ)
    {w : ℂ}
    (hw : 0 < w.re)
    (T : ℝ)
    (hT : 0 < T) :
    Tendsto
      (fun ε : ℝ =>
        Complex.finiteAbelPlanaLogRightVerticalCotangentRemainderSidePVNormalized N w T ε)
      (𝓝[>] (0 : ℝ))
      (𝓝 (-Complex.finiteAbelPlanaLogUpperVerticalIntegralUpTo N w T)) := by
  have hevent :
      ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ),
        Complex.finiteAbelPlanaLogRightVerticalCotangentRemainderSidePVNormalized N w T ε =
          -Complex.finiteAbelPlanaLogUpperVerticalIntegralFromTo N w ε T := by
    filter_upwards [Ioo_mem_nhdsWithin_Ioi ⟨le_rfl, hT⟩] with ε hε
    exact
      Complex.finiteAbelPlana_log_rightVerticalRemainderPV_eq_cutoffUpperVertical
        N w T ε hε.1 hε.2
  have hlim :
      Tendsto
        (fun ε : ℝ =>
          -Complex.finiteAbelPlanaLogUpperVerticalIntegralFromTo N w ε T)
        (𝓝[>] (0 : ℝ))
        (𝓝 (-Complex.finiteAbelPlanaLogUpperVerticalIntegralUpTo N w T)) :=
    (Complex.finiteAbelPlana_log_upperVerticalIntegralFromTo_tendsto_upTo
      N hw T hT).neg
  have hevent_symm :
      (fun ε : ℝ =>
          -Complex.finiteAbelPlanaLogUpperVerticalIntegralFromTo N w ε T) =ᶠ[𝓝[>] (0 : ℝ)]
        (fun ε : ℝ =>
          Complex.finiteAbelPlanaLogRightVerticalCotangentRemainderSidePVNormalized N w T ε) :=
    hevent.mono (fun ε hε => hε.symm)
  exact hlim.congr' hevent_symm

/-- Principal-value left endpoint boundary-face convergence. -/
theorem Complex.finiteAbelPlana_log_leftBoundaryFacePV_tendsto_lowerNamedBoundaryFace
    (N : ℕ)
    {w : ℂ}
    (hw : 0 < w.re)
    (T : ℝ)
    (hT : 0 < T) :
    Tendsto
      (fun ε : ℝ =>
        Complex.finiteAbelPlanaLogLeftBoundaryFacePVNormalized N w T ε)
      (𝓝[>] (0 : ℝ))
      (𝓝
        ((((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹ *
            (-Complex.finiteAbelPlanaLogUpperHorizontalCotangentConstantSide N w T -
              Complex.I * Complex.finiteAbelPlanaLogLeftVerticalCotangentConstantSide w T)) +
          (-Complex.finiteAbelPlanaLogLowerVerticalIntegralUpTo w T))) := by
  have hconst :
      Tendsto
        (fun ε : ℝ =>
          ((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹ *
            (-Complex.finiteAbelPlanaLogUpperHorizontalCotangentConstantSide N w T -
              Complex.I * Complex.finiteAbelPlanaLogLeftVerticalCotangentConstantSidePV w T ε))
        (𝓝[>] (0 : ℝ))
        (𝓝
          (((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹ *
            (-Complex.finiteAbelPlanaLogUpperHorizontalCotangentConstantSide N w T -
              Complex.I * Complex.finiteAbelPlanaLogLeftVerticalCotangentConstantSide w T))) :=
    Complex.finiteAbelPlana_log_leftConstantKernelPV_tendsto_realEndpoint
      N hw T hT
  have hrem :
      Tendsto
        (fun ε : ℝ =>
          Complex.finiteAbelPlanaLogLeftVerticalCotangentRemainderSidePVNormalized w T ε)
        (𝓝[>] (0 : ℝ))
        (𝓝 (-Complex.finiteAbelPlanaLogLowerVerticalIntegralUpTo w T)) :=
    Complex.finiteAbelPlana_log_leftVerticalRemainderPV_tendsto_lowerVertical
      hw T hT
  have hsum := hconst.add hrem
  have hpoint :
      (fun ε : ℝ =>
        Complex.finiteAbelPlanaLogLeftBoundaryFacePVNormalized N w T ε) =
      (fun ε : ℝ =>
        ((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹ *
          (-Complex.finiteAbelPlanaLogUpperHorizontalCotangentConstantSide N w T -
            Complex.I * Complex.finiteAbelPlanaLogLeftVerticalCotangentConstantSidePV w T ε) +
          Complex.finiteAbelPlanaLogLeftVerticalCotangentRemainderSidePVNormalized w T ε) := by
    exact funext (fun ε => rfl)
  exact hpoint ▸ hsum

/-- Principal-value right endpoint boundary-face convergence. -/
theorem Complex.finiteAbelPlana_log_rightBoundaryFacePV_tendsto_upperNamedBoundaryFace
    (N : ℕ)
    {w : ℂ}
    (hw : 0 < w.re)
    (T : ℝ)
    (hT : 0 < T) :
    Tendsto
      (fun ε : ℝ =>
        Complex.finiteAbelPlanaLogRightBoundaryFacePVNormalized N w T ε)
      (𝓝[>] (0 : ℝ))
      (𝓝
        ((((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹ *
            (Complex.finiteAbelPlanaLogLowerHorizontalCotangentConstantSide N w T +
              Complex.I *
                Complex.finiteAbelPlanaLogRightVerticalCotangentConstantSide N w T)) +
          (-Complex.finiteAbelPlanaLogUpperVerticalIntegralUpTo N w T))) := by
  have hconst :
      Tendsto
        (fun ε : ℝ =>
          ((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹ *
            (Complex.finiteAbelPlanaLogLowerHorizontalCotangentConstantSide N w T +
              Complex.I *
                Complex.finiteAbelPlanaLogRightVerticalCotangentConstantSidePV N w T ε))
        (𝓝[>] (0 : ℝ))
        (𝓝
          (((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹ *
            (Complex.finiteAbelPlanaLogLowerHorizontalCotangentConstantSide N w T +
              Complex.I *
                Complex.finiteAbelPlanaLogRightVerticalCotangentConstantSide N w T))) :=
    Complex.finiteAbelPlana_log_rightConstantKernelPV_tendsto_zero
      N hw T hT
  have hrem :
      Tendsto
        (fun ε : ℝ =>
          Complex.finiteAbelPlanaLogRightVerticalCotangentRemainderSidePVNormalized N w T ε)
        (𝓝[>] (0 : ℝ))
        (𝓝 (-Complex.finiteAbelPlanaLogUpperVerticalIntegralUpTo N w T)) :=
    Complex.finiteAbelPlana_log_rightVerticalRemainderPV_tendsto_upperVertical
      N hw T hT
  have hsum := hconst.add hrem
  have hpoint :
      (fun ε : ℝ =>
        Complex.finiteAbelPlanaLogRightBoundaryFacePVNormalized N w T ε) =
      (fun ε : ℝ =>
        ((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹ *
          (Complex.finiteAbelPlanaLogLowerHorizontalCotangentConstantSide N w T +
            Complex.I *
              Complex.finiteAbelPlanaLogRightVerticalCotangentConstantSidePV N w T ε) +
          Complex.finiteAbelPlanaLogRightVerticalCotangentRemainderSidePVNormalized N w T ε) := by
    exact funext (fun ε => rfl)
  exact hpoint ▸ hsum

/-- Principal-value boundary-face reconstruction. -/
theorem Complex.finiteAbelPlana_log_boundaryFacesPV_tendsto_namedBoundary
    (N : ℕ)
    {w : ℂ}
    (hw : 0 < w.re)
    (T : ℝ)
    (hT : 0 < T) :
    Tendsto
      (fun ε : ℝ =>
        Complex.finiteAbelPlanaLogLeftBoundaryFacePVNormalized N w T ε +
          Complex.finiteAbelPlanaLogRightBoundaryFacePVNormalized N w T ε)
      (𝓝[>] (0 : ℝ))
      (𝓝
        (((((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹ *
              (-Complex.finiteAbelPlanaLogUpperHorizontalCotangentConstantSide N w T -
                Complex.I * Complex.finiteAbelPlanaLogLeftVerticalCotangentConstantSide w T)) +
            (-Complex.finiteAbelPlanaLogLowerVerticalIntegralUpTo w T)) +
          ((((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹ *
              (Complex.finiteAbelPlanaLogLowerHorizontalCotangentConstantSide N w T +
                Complex.I *
                  Complex.finiteAbelPlanaLogRightVerticalCotangentConstantSide N w T)) +
            (-Complex.finiteAbelPlanaLogUpperVerticalIntegralUpTo N w T)))) := by
  have hleft :
      Tendsto
        (fun ε : ℝ =>
          Complex.finiteAbelPlanaLogLeftBoundaryFacePVNormalized N w T ε)
        (𝓝[>] (0 : ℝ))
        (𝓝
          ((((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹ *
              (-Complex.finiteAbelPlanaLogUpperHorizontalCotangentConstantSide N w T -
                Complex.I * Complex.finiteAbelPlanaLogLeftVerticalCotangentConstantSide w T)) +
            (-Complex.finiteAbelPlanaLogLowerVerticalIntegralUpTo w T))) :=
    Complex.finiteAbelPlana_log_leftBoundaryFacePV_tendsto_lowerNamedBoundaryFace
      N hw T hT
  have hright :
      Tendsto
        (fun ε : ℝ =>
          Complex.finiteAbelPlanaLogRightBoundaryFacePVNormalized N w T ε)
        (𝓝[>] (0 : ℝ))
        (𝓝
          ((((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹ *
              (Complex.finiteAbelPlanaLogLowerHorizontalCotangentConstantSide N w T +
                Complex.I *
                  Complex.finiteAbelPlanaLogRightVerticalCotangentConstantSide N w T)) +
            (-Complex.finiteAbelPlanaLogUpperVerticalIntegralUpTo N w T))) :=
    Complex.finiteAbelPlana_log_rightBoundaryFacePV_tendsto_upperNamedBoundaryFace
      N hw T hT
  have hsum :
      Tendsto
        (fun ε : ℝ =>
          Complex.finiteAbelPlanaLogLeftBoundaryFacePVNormalized N w T ε +
            Complex.finiteAbelPlanaLogRightBoundaryFacePVNormalized N w T ε)
        (𝓝[>] (0 : ℝ))
        (𝓝
          (((((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹ *
                (-Complex.finiteAbelPlanaLogUpperHorizontalCotangentConstantSide N w T -
                  Complex.I * Complex.finiteAbelPlanaLogLeftVerticalCotangentConstantSide w T)) +
              (-Complex.finiteAbelPlanaLogLowerVerticalIntegralUpTo w T)) +
            ((((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹ *
                (Complex.finiteAbelPlanaLogLowerHorizontalCotangentConstantSide N w T +
                  Complex.I *
                    Complex.finiteAbelPlanaLogRightVerticalCotangentConstantSide N w T)) +
              (-Complex.finiteAbelPlanaLogUpperVerticalIntegralUpTo N w T)))) :=
    hleft.add hright
  exact hsum

end

end LFunctions
end Boundary
