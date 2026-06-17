import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.GammaBinetStirling.Binet.Algebraic.Owner

/-!
# Binet formula: logarithmic and arctangent derivatives

This file owns logarithmic derivative formulas for the arctangent kernel
and the main-term Binet derivatives.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped Topology

    (x a b : ℂ) :
    (x + a) - (a + -b) = x + b := by
  calc
    (x + a) - (a + -b) = (x + a) + -(a + -b) :=
      sub_eq_add_neg (x + a) (a + -b)
    _ = (x + a) + (-a + -(-b)) := by
      exact congrArg (fun u : ℂ => (x + a) + u) (neg_add_rev a (-b))
    _ = (x + a) + (-a + b) := by
      exact congrArg (fun u : ℂ => (x + a) + (-a + u)) (neg_neg b)
    _ = x + (a + (-a + b)) := by
      exact add_assoc x a (-a + b)
    _ = x + ((a + -a) + b) := by
      exact congrArg (fun u : ℂ => x + u) (Eq.symm (add_assoc a (-a) b))
    _ = x + (0 + b) := by
      exact congrArg (fun u : ℂ => x + (u + b)) (add_neg_cancel a)
    _ = x + b := by
      exact congrArg (fun u : ℂ => x + u) (zero_add b)

/-- Removing the same unit after subtracting a term leaves the negative term. -/
theorem Complex.one_sub_sub_one_eq_neg
    (h : ℂ) :
    (1 - h) - 1 = -h := by
  calc
    (1 - h) - 1 = (1 + -h) + -1 := by
      exact congrArg (fun u : ℂ => u + -1) (sub_eq_add_neg 1 h)
    _ = 1 + (-h + -1) := add_assoc 1 (-h) (-1)
    _ = 1 + (-1 + -h) := by
      exact congrArg (fun u : ℂ => 1 + u) (add_comm (-h) (-1))
    _ = (1 + -1) + -h := by
      exact Eq.symm (add_assoc 1 (-1) (-h))
    _ = 0 + -h := by
      exact congrArg (fun u : ℂ => u + -h) (add_neg_cancel 1)
    _ = -h := zero_add (-h)

/-- The final additive cancellation in the Binet main-term derivative. -/
theorem Complex.add_one_sub_sub_one_eq_sub
    (L h : ℂ) :
    (L + (1 - h)) - 1 = L - h := by
  calc
    (L + (1 - h)) - 1 = L + ((1 - h) - 1) := by
      exact Eq.symm (add_sub_assoc L (1 - h) 1)
    _ = L + -h := by
      exact congrArg (fun u : ℂ => L + u)
        (Complex.one_sub_sub_one_eq_neg h)
    _ = L - h := by
      exact Eq.symm (sub_eq_add_neg L h)

/-- The two linear factors in the arctangent logarithmic derivative multiply
to `1 + z^2`. -/
theorem Complex.one_sub_mul_I_mul_one_add_mul_I
    (z : ℂ) :
    (1 - z * Complex.I) * (1 + z * Complex.I) = 1 + z ^ 2 := by
  have hsquare :
      (z * Complex.I) * (z * Complex.I) = -z ^ 2 := by
    calc
      (z * Complex.I) * (z * Complex.I) =
          (z * z) * (Complex.I * Complex.I) := by
        exact mul_mul_mul_comm z Complex.I z Complex.I
      _ = (z * z) * (-1 : ℂ) := by
        exact congrArg (fun u : ℂ => (z * z) * u) Complex.I_mul_I
      _ = -(z * z) := mul_neg_one (z * z)
      _ = -z ^ 2 := by
        exact congrArg Neg.neg (Eq.symm (sq z))
  calc
    (1 - z * Complex.I) * (1 + z * Complex.I) =
        1 * (1 + z * Complex.I) - (z * Complex.I) * (1 + z * Complex.I) := by
      exact sub_mul 1 (z * Complex.I) (1 + z * Complex.I)
    _ = (1 + z * Complex.I) -
        ((z * Complex.I) * 1 + (z * Complex.I) * (z * Complex.I)) := by
      exact congrArg₂ HSub.hSub
        (one_mul (1 + z * Complex.I))
        (mul_add (z * Complex.I) 1 (z * Complex.I))
    _ = (1 + z * Complex.I) -
        (z * Complex.I + (z * Complex.I) * (z * Complex.I)) := by
      exact congrArg
        (fun u : ℂ => (1 + z * Complex.I) - (u + (z * Complex.I) * (z * Complex.I)))
        (mul_one (z * Complex.I))
    _ = (1 + z * Complex.I) - (z * Complex.I + -z ^ 2) := by
      exact congrArg
        (fun u : ℂ => (1 + z * Complex.I) - (z * Complex.I + u))
        hsquare
    _ = 1 + z ^ 2 := by
      exact Complex.add_sub_add_neg_right_eq_add 1 (z * Complex.I) (z ^ 2)

/-- The scalar normalization in the logarithmic formula for `arctan`. -/
theorem Complex.neg_I_div_two_mul_two_I_eq_one :
    (-Complex.I / 2) * ((2 : ℂ) * Complex.I) = 1 := by
  calc
    (-Complex.I / 2) * ((2 : ℂ) * Complex.I) =
        ((-Complex.I / 2) * (2 : ℂ)) * Complex.I := by
      exact mul_assoc (-Complex.I / 2) (2 : ℂ) Complex.I
    _ = -Complex.I * Complex.I := by
      exact congrArg (fun u : ℂ => u * Complex.I)
        (div_mul_cancel₀ (-Complex.I) (two_ne_zero' ℂ))
    _ = -(Complex.I * Complex.I) := by
      exact neg_mul Complex.I Complex.I
    _ = -(-1 : ℂ) := by
      exact congrArg Neg.neg Complex.I_mul_I
    _ = 1 := neg_neg (1 : ℂ)

/-- Denominator cancellation for the logarithmic derivative expression in the
principal arctangent formula. -/
theorem Complex.arctan_log_derivative_factor_algebra
    (z : ℂ)
    (hden_ne : 1 - z * Complex.I ≠ 0) :
    (-Complex.I / 2) *
        (((2 : ℂ) * Complex.I / (1 - z * Complex.I) ^ 2) /
          ((1 + z * Complex.I) / (1 - z * Complex.I))) =
      (1 : ℂ) / (1 + z ^ 2) := by
  have hquot :
      (((2 : ℂ) * Complex.I / (1 - z * Complex.I) ^ 2) /
          ((1 + z * Complex.I) / (1 - z * Complex.I))) =
        ((2 : ℂ) * Complex.I) /
          ((1 - z * Complex.I) * (1 + z * Complex.I)) := by
    have hden_sq :
        (1 - z * Complex.I) ^ 2 =
          (1 - z * Complex.I) * (1 - z * Complex.I) := by
      exact sq (1 - z * Complex.I)
    calc
      (((2 : ℂ) * Complex.I / (1 - z * Complex.I) ^ 2) /
          ((1 + z * Complex.I) / (1 - z * Complex.I))) =
          (((2 : ℂ) * Complex.I /
              ((1 - z * Complex.I) * (1 - z * Complex.I))) /
            ((1 + z * Complex.I) / (1 - z * Complex.I))) := by
        exact congrArg
          (fun u : ℂ =>
            (((2 : ℂ) * Complex.I / u) /
              ((1 + z * Complex.I) / (1 - z * Complex.I))))
          hden_sq
      _ =
          ((((2 : ℂ) * Complex.I) / (1 - z * Complex.I) /
              (1 - z * Complex.I)) /
            ((1 + z * Complex.I) / (1 - z * Complex.I))) := by
        exact congrArg
          (fun u : ℂ => u / ((1 + z * Complex.I) / (1 - z * Complex.I)))
          (Eq.symm (div_div ((2 : ℂ) * Complex.I)
            (1 - z * Complex.I) (1 - z * Complex.I)))
      _ = (((2 : ℂ) * Complex.I) / (1 - z * Complex.I)) /
            (1 + z * Complex.I) := by
        exact div_div_div_cancel_right₀ hden_ne
          (((2 : ℂ) * Complex.I) / (1 - z * Complex.I))
          (1 + z * Complex.I)
      _ = ((2 : ℂ) * Complex.I) /
            ((1 - z * Complex.I) * (1 + z * Complex.I)) := by
        exact div_div ((2 : ℂ) * Complex.I)
          (1 - z * Complex.I) (1 + z * Complex.I)
  have hfactor :
      (1 - z * Complex.I) * (1 + z * Complex.I) = 1 + z ^ 2 :=
    Complex.one_sub_mul_I_mul_one_add_mul_I z
  calc
    (-Complex.I / 2) *
        (((2 : ℂ) * Complex.I / (1 - z * Complex.I) ^ 2) /
          ((1 + z * Complex.I) / (1 - z * Complex.I))) =
        (-Complex.I / 2) *
          (((2 : ℂ) * Complex.I) /
            ((1 - z * Complex.I) * (1 + z * Complex.I))) := by
      exact congrArg (fun u : ℂ => (-Complex.I / 2) * u) hquot
    _ = ((-Complex.I / 2) * ((2 : ℂ) * Complex.I)) /
          ((1 - z * Complex.I) * (1 + z * Complex.I)) := by
      exact Eq.symm
        (mul_div_assoc (-Complex.I / 2) ((2 : ℂ) * Complex.I)
          ((1 - z * Complex.I) * (1 + z * Complex.I)))
    _ = (1 : ℂ) / ((1 - z * Complex.I) * (1 + z * Complex.I)) := by
      exact congrArg
        (fun u : ℂ => u / ((1 - z * Complex.I) * (1 + z * Complex.I)))
        Complex.neg_I_div_two_mul_two_I_eq_one
    _ = (1 : ℂ) / (1 + z ^ 2) := by
      exact congrArg (fun u : ℂ => (1 : ℂ) / u) hfactor

/-- The denominator identity used after composing the arctangent derivative
with `z ↦ a / z`. -/
theorem Complex.one_add_sq_div_eq_sq_add_sq_div_sq
    {a w : ℂ}
    (hw_ne : w ≠ 0) :
    1 + (a / w) ^ 2 = (w ^ 2 + a ^ 2) / w ^ 2 := by
  have hw_sq_ne : w ^ 2 ≠ 0 :=
    pow_ne_zero 2 hw_ne
  calc
    1 + (a / w) ^ 2 = w ^ 2 / w ^ 2 + (a / w) ^ 2 := by
      exact congrArg (fun u : ℂ => u + (a / w) ^ 2)
        (Eq.symm (div_self hw_sq_ne))
    _ = w ^ 2 / w ^ 2 + a ^ 2 / w ^ 2 := by
      exact congrArg (fun u : ℂ => w ^ 2 / w ^ 2 + u)
        (div_pow a w 2)
    _ = (w ^ 2 + a ^ 2) / w ^ 2 := by
      exact Eq.symm (div_add_div_same (w ^ 2) (a ^ 2) (w ^ 2))

/-- Algebraic normalization of the chain-rule derivative of
`z ↦ arctan (a / z)`. -/
theorem Complex.arctan_t_div_derivative_algebra
    {a w : ℂ}
    (hw_ne : w ≠ 0) :
    ((1 : ℂ) / (1 + (a / w) ^ 2)) *
        (-a / w ^ 2) =
      -a / (w ^ 2 + a ^ 2) := by
  have hw_sq_ne : w ^ 2 ≠ 0 :=
    pow_ne_zero 2 hw_ne
  have hden_eq :
      1 + (a / w) ^ 2 = (w ^ 2 + a ^ 2) / w ^ 2 :=
    Complex.one_add_sq_div_eq_sq_add_sq_div_sq hw_ne
  calc
    ((1 : ℂ) / (1 + (a / w) ^ 2)) *
        (-a / w ^ 2) =
        ((1 : ℂ) / ((w ^ 2 + a ^ 2) / w ^ 2)) *
          (-a / w ^ 2) := by
      exact congrArg (fun u : ℂ => ((1 : ℂ) / u) * (-a / w ^ 2)) hden_eq
    _ = (w ^ 2 / (w ^ 2 + a ^ 2)) * (-a / w ^ 2) := by
      exact congrArg (fun u : ℂ => u * (-a / w ^ 2))
        (one_div_div (w ^ 2 + a ^ 2) (w ^ 2))
    _ = (-a / w ^ 2) * (w ^ 2 / (w ^ 2 + a ^ 2)) := by
      exact mul_comm (w ^ 2 / (w ^ 2 + a ^ 2)) (-a / w ^ 2)
    _ = -a / (w ^ 2 + a ^ 2) := by
      exact div_mul_div_cancel₀ hw_sq_ne (-a) (w ^ 2 + a ^ 2)

/-- The reciprocal half-factor in the Binet main-term derivative. -/
theorem Complex.one_half_mul_one_div_eq_one_div_two_mul
    {w : ℂ}
    (hw : w ≠ 0) :
    (1 / 2 : ℂ) * (1 / w) = 1 / (2 * w) := by
  have htwo : (2 : ℂ) ≠ 0 := by
    exact two_ne_zero
  have hprod : (2 : ℂ) * w ≠ 0 :=
    mul_ne_zero htwo hw
  apply (mul_left_cancel₀ hprod)
  calc
    (2 * w) * ((1 / 2 : ℂ) * (1 / w)) =
        (2 * (1 / 2 : ℂ)) * (w * (1 / w)) := by
      exact mul_mul_mul_comm (2 : ℂ) w (1 / 2 : ℂ) (1 / w)
    _ = 1 * 1 := by
      exact congrArg₂ HMul.hMul
        (mul_one_div_cancel htwo)
        (mul_one_div_cancel hw)
    _ = 1 := one_mul (1 : ℂ)
    _ = (2 * w) * (1 / (2 * w)) := by
      exact Eq.symm (mul_one_div_cancel hprod)

/-- Algebraic normalization of the Binet main-term derivative. -/
theorem Complex.binetLogGammaMainTerm_derivative_algebra
    {w L : ℂ}
    (hw : w ≠ 0) :
    (1 * L + (w - (1 / 2 : ℂ)) * (1 / w)) - 1 + 0 =
      L - (1 / (2 * w)) := by
  have hw_cancel : w * (1 / w) = 1 :=
    mul_one_div_cancel hw
  have hhalf :
      (1 / 2 : ℂ) * (1 / w) = 1 / (2 * w) :=
    Complex.one_half_mul_one_div_eq_one_div_two_mul hw
  calc
    (1 * L + (w - (1 / 2 : ℂ)) * (1 / w)) - 1 + 0 =
        (L + (w - (1 / 2 : ℂ)) * (1 / w)) - 1 := by
      calc
        (1 * L + (w - (1 / 2 : ℂ)) * (1 / w)) - 1 + 0 =
            (L + (w - (1 / 2 : ℂ)) * (1 / w)) - 1 + 0 := by
          exact congrArg
            (fun u : ℂ => (u + (w - (1 / 2 : ℂ)) * (1 / w)) - 1 + 0)
            (one_mul L)
        _ = (L + (w - (1 / 2 : ℂ)) * (1 / w)) - 1 :=
          add_zero ((L + (w - (1 / 2 : ℂ)) * (1 / w)) - 1)
    _ = (L + (w * (1 / w) - (1 / 2 : ℂ) * (1 / w))) - 1 := by
      exact congrArg (fun u : ℂ => (L + u) - 1)
        (sub_mul w (1 / 2 : ℂ) (1 / w))
    _ = (L + (1 - (1 / 2 : ℂ) * (1 / w))) - 1 := by
      exact congrArg
        (fun u : ℂ => (L + (u - (1 / 2 : ℂ) * (1 / w))) - 1)
        hw_cancel
    _ = (L + (1 - 1 / (2 * w))) - 1 := by
      exact congrArg (fun u : ℂ => (L + (1 - u)) - 1) hhalf
    _ = L - (1 / (2 * w)) := by
      exact Complex.add_one_sub_sub_one_eq_sub L (1 / (2 * w))

/-- Factoring `z^2 + t^2` into the two imaginary translates. -/
theorem Complex.add_mul_sub_real_mul_I_eq_sq_add_sq

end

end LFunctions
end Boundary
