import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.GammaBinetStirling.BinetAbelPlana
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.GammaBinetStirling.BinetMajorant
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.GammaBinetStirling.BinetKernelBounds
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.SpecialFunctions.Complex.Arctan

/-!
# Binet formula: algebraic fundamentals

This file owns basic arithmetic properties and complex number algebra used
throughout the Binet kernel analysis.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped Topology

theorem Real.half_eq_self_add_neg_half
    (x : ℝ) :
    x / 2 = x + (-(x / 2)) := by
  calc
    x / 2 = x / 2 + 0 := Eq.symm (add_zero (x / 2))
    _ = x / 2 + (x / 2 + -(x / 2)) := by
      exact congrArg (fun z : ℝ => x / 2 + z) (Eq.symm (add_neg_cancel (x / 2)))
    _ = (x / 2 + x / 2) + -(x / 2) := by
      exact Eq.symm (add_assoc (x / 2) (x / 2) (-(x / 2)))
    _ = x + (-(x / 2)) := by
      exact congrArg (fun z : ℝ => z + (-(x / 2))) (add_halves x)

/-- Translating by the displacement from `x` to `y` lands at `y`. -/
theorem Real.add_sub_self_right
    (x y : ℝ) :
    x + (y - x) = y := by
  calc
    x + (y - x) = x + y - x := by
      exact (add_sub_assoc x y x).symm
    _ = y := add_sub_cancel_left x y

/-- Division by a square followed by division by `d` can be factored by the
inverse square. -/
theorem Real.div_sq_div_assoc
    (δ d t : ℝ) :
    (t / δ ^ 2) / d = (1 / δ ^ 2) * (t / d) := by
  calc
    (t / δ ^ 2) / d = (t * (δ ^ 2)⁻¹) * d⁻¹ := rfl
    _ = t * ((δ ^ 2)⁻¹ * d⁻¹) := by
      exact mul_assoc t (δ ^ 2)⁻¹ d⁻¹
    _ = (δ ^ 2)⁻¹ * (t * d⁻¹) := by
      exact mul_left_comm t (δ ^ 2)⁻¹ d⁻¹
    _ = (1 * (δ ^ 2)⁻¹) * (t * d⁻¹) := by
      exact congrArg (fun z : ℝ => z * (t * d⁻¹)) (Eq.symm (one_mul (δ ^ 2)⁻¹))
    _ = (1 / δ ^ 2) * (t / d) := rfl

/-- A complex number identified with a real coercion has zero imaginary part. -/
theorem Complex.im_eq_zero_of_eq_ofReal
    {z : ℂ}
    {x : ℝ}
    (hz : z = (x : ℂ)) :
    z.im = 0 := by
  calc
    z.im = ((x : ℂ) : ℂ).im := congrArg Complex.im hz
    _ = 0 := Complex.ofReal_im x

/-- Squaring a real multiple of `I` gives the negative real square. -/
theorem Complex.real_mul_I_sq
    (t : ℝ) :
    ((t : ℂ) * Complex.I) ^ 2 = -((t : ℂ) ^ 2) := by
  calc
    ((t : ℂ) * Complex.I) ^ 2 =
        ((t : ℂ) * Complex.I) * ((t : ℂ) * Complex.I) := sq _
    _ = ((t : ℂ) * (t : ℂ)) * (Complex.I * Complex.I) := by
      exact mul_mul_mul_comm (t : ℂ) Complex.I (t : ℂ) Complex.I
    _ = ((t : ℂ) * (t : ℂ)) * (-1 : ℂ) := by
      exact congrArg (fun z : ℂ => ((t : ℂ) * (t : ℂ)) * z) Complex.I_mul_I
    _ = -((t : ℂ) * (t : ℂ)) := mul_neg_one ((t : ℂ) * (t : ℂ))
    _ = -((t : ℂ) ^ 2) := by
      exact congrArg Neg.neg (Eq.symm (sq (t : ℂ)))

/-- Dividing `-1` by `I` gives `I`. -/
theorem Complex.neg_one_div_I_eq_I :
    ((-1 : ℂ) / Complex.I) = Complex.I := by
  calc
    ((-1 : ℂ) / Complex.I) = -((-1 : ℂ) * Complex.I) :=
      Complex.div_I (-1 : ℂ)
    _ = -(-Complex.I) := by
      exact congrArg Neg.neg (neg_one_mul Complex.I)
    _ = Complex.I := neg_neg Complex.I

/-- Dividing `1` by `I` gives `-I`. -/
theorem Complex.one_div_I_eq_neg_I :
    ((1 : ℂ) / Complex.I) = -Complex.I := by
  calc
    ((1 : ℂ) / Complex.I) = -((1 : ℂ) * Complex.I) :=
      Complex.div_I (1 : ℂ)
    _ = -Complex.I := by
      exact congrArg Neg.neg (one_mul Complex.I)

/-- The branch equation `t / w = I` would force `w + tI = 0`. -/
theorem Complex.add_I_mul_mul_I_eq_zero
    (w : ℂ) :
    w + (Complex.I * w) * Complex.I = 0 := by
  have hmul : (Complex.I * w) * Complex.I = -w := by
    calc
      (Complex.I * w) * Complex.I = Complex.I * (w * Complex.I) :=
        mul_assoc Complex.I w Complex.I
      _ = Complex.I * (Complex.I * w) := by
        exact congrArg (fun z : ℂ => Complex.I * z) (mul_comm w Complex.I)
      _ = (Complex.I * Complex.I) * w := by
        exact Eq.symm (mul_assoc Complex.I Complex.I w)
      _ = (-1 : ℂ) * w := by
        exact congrArg (fun z : ℂ => z * w) Complex.I_mul_I
      _ = -w := neg_one_mul w
  calc
    w + (Complex.I * w) * Complex.I = w + (-w) := by
      exact congrArg (fun z : ℂ => w + z) hmul
    _ = 0 := add_neg_cancel w

/-- The branch equation `t / w = -I` would force `w - tI = 0`. -/
theorem Complex.sub_neg_I_mul_mul_I_eq_zero
    (w : ℂ) :
    w - (-Complex.I * w) * Complex.I = 0 := by
  have hmul : (-Complex.I * w) * Complex.I = w := by
    calc
      (-Complex.I * w) * Complex.I = -Complex.I * (w * Complex.I) :=
        mul_assoc (-Complex.I) w Complex.I
      _ = -Complex.I * (Complex.I * w) := by
        exact congrArg (fun z : ℂ => -Complex.I * z) (mul_comm w Complex.I)
      _ = (-Complex.I * Complex.I) * w := by
        exact Eq.symm (mul_assoc (-Complex.I) Complex.I w)
      _ = (-(Complex.I * Complex.I)) * w := by
        exact congrArg (fun z : ℂ => z * w) (neg_mul Complex.I Complex.I)
      _ = (-(-1 : ℂ)) * w := by
        exact congrArg (fun z : ℂ => z * w)
          (congrArg Neg.neg Complex.I_mul_I)
      _ = (1 : ℂ) * w := by
        exact congrArg (fun z : ℂ => z * w) (neg_neg (1 : ℂ))
      _ = w := one_mul w
  calc
    w - (-Complex.I * w) * Complex.I = w - w := by
      exact congrArg (fun z : ℂ => w - z) hmul
    _ = 0 := sub_self w

/-- Collecting one additive cancellation without commutative-group automation. -/
theorem Complex.add_sub_add_neg_right_eq_add
    (x a b : ℂ) :
    (x + a) - (a + -b) = x + b := by
  calc
    (x + a) - (a + -b) = (x + a) + -(a + -b) :=
      sub_eq_add_neg (x + a) (a + -b)
    _ = (x + a) + (-(-b) + -a) := by
      exact congrArg (fun u : ℂ => (x + a) + u) (neg_add_rev a (-b))
    _ = (x + a) + (b + -a) := by
      exact congrArg (fun u : ℂ => (x + a) + (u + -a)) (neg_neg b)
    _ = (x + a) + (-a + b) := by
      exact congrArg (fun u : ℂ => (x + a) + u) (add_comm b (-a))
    _ = x + (a + (-a + b)) := by
      exact add_assoc x a (-a + b)
    _ = x + ((a + -a) + b) := by
      exact congrArg (fun u : ℂ => x + u) (Eq.symm (add_assoc a (-a) b))
    _ = x + (0 + b) := by
      exact congrArg (fun u : ℂ => x + (u + b)) (add_neg_cancel a)
    _ = x + b := by
      exact congrArg (fun u : ℂ => x + u) (zero_add b)

end

end LFunctions
end Boundary
