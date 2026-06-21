import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.PoleClearedBoundarySetup.Core.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.GammaBoundaryPL.DampedFamily.Owner
import Mathlib.Data.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Left-boundary Gamma argument lemmas

This file owns the fixed-real-part rewrites and vertical half-tail lemmas used by the
left-boundary Stirling estimates.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped Filter Topology
local notation "π" => Real.pi

/-- The real part of a real multiple of `I` is zero. -/
private theorem complex_ofReal_mul_I_re_eq_zero
    (b : ℝ) :
    (((b : ℝ) : ℂ) * Complex.I).re = 0 := by
  calc
    (((b : ℝ) : ℂ) * Complex.I).re =
        ((b : ℝ) : ℂ).re * Complex.I.re -
          ((b : ℝ) : ℂ).im * Complex.I.im := by
      exact Complex.mul_re ((b : ℝ) : ℂ) Complex.I
    _ = b * Complex.I.re - ((b : ℝ) : ℂ).im * Complex.I.im := by
      exact congrArg
        (fun x : ℝ => x * Complex.I.re - ((b : ℝ) : ℂ).im * Complex.I.im)
        (Complex.ofReal_re b)
    _ = b * 0 - ((b : ℝ) : ℂ).im * Complex.I.im := by
      exact congrArg
        (fun x : ℝ => b * x - ((b : ℝ) : ℂ).im * Complex.I.im)
        Complex.I_re
    _ = b * 0 - 0 * Complex.I.im := by
      exact congrArg
        (fun x : ℝ => b * 0 - x * Complex.I.im)
        (Complex.ofReal_im b)
    _ = b * 0 - 0 * 1 := by
      exact congrArg (fun x : ℝ => b * 0 - 0 * x) Complex.I_im
    _ = 0 - 0 * 1 := by
      exact congrArg (fun x : ℝ => x - 0 * 1) (mul_zero b)
    _ = 0 - 0 := by
      exact congrArg (fun x : ℝ => 0 - x) (zero_mul 1)
    _ = 0 := by
      exact sub_zero 0

/-- The imaginary part of a real multiple of `I` is the multiplier. -/
private theorem complex_ofReal_mul_I_im_eq
    (b : ℝ) :
    (((b : ℝ) : ℂ) * Complex.I).im = b := by
  calc
    (((b : ℝ) : ℂ) * Complex.I).im =
        ((b : ℝ) : ℂ).re * Complex.I.im +
          ((b : ℝ) : ℂ).im * Complex.I.re := by
      exact Complex.mul_im ((b : ℝ) : ℂ) Complex.I
    _ = b * Complex.I.im + ((b : ℝ) : ℂ).im * Complex.I.re := by
      exact congrArg
        (fun x : ℝ => x * Complex.I.im + ((b : ℝ) : ℂ).im * Complex.I.re)
        (Complex.ofReal_re b)
    _ = b * 1 + ((b : ℝ) : ℂ).im * Complex.I.re := by
      exact congrArg
        (fun x : ℝ => b * x + ((b : ℝ) : ℂ).im * Complex.I.re)
        Complex.I_im
    _ = b * 1 + 0 * Complex.I.re := by
      exact congrArg
        (fun x : ℝ => b * 1 + x * Complex.I.re)
        (Complex.ofReal_im b)
    _ = b * 1 + 0 * 0 := by
      exact congrArg (fun x : ℝ => b * 1 + 0 * x) Complex.I_re
    _ = b + 0 * 0 := by
      exact congrArg (fun x : ℝ => x + 0 * 0) (mul_one b)
    _ = b + 0 := by
      exact congrArg (fun x : ℝ => b + x) (zero_mul 0)
    _ = b := by
      exact add_zero b

/-- Coordinates of the standard vertical parametrization: real part. -/
private theorem complex_ofReal_add_ofReal_mul_I_re_eq
    (a b : ℝ) :
    (((a : ℝ) : ℂ) + ((b : ℝ) : ℂ) * Complex.I).re = a := by
  calc
    (((a : ℝ) : ℂ) + ((b : ℝ) : ℂ) * Complex.I).re =
        ((a : ℝ) : ℂ).re + (((b : ℝ) : ℂ) * Complex.I).re := by
      exact Complex.add_re ((a : ℝ) : ℂ) (((b : ℝ) : ℂ) * Complex.I)
    _ = a + (((b : ℝ) : ℂ) * Complex.I).re := by
      exact congrArg
        (fun x : ℝ => x + (((b : ℝ) : ℂ) * Complex.I).re)
        (Complex.ofReal_re a)
    _ = a + 0 := by
      exact congrArg (fun x : ℝ => a + x) (complex_ofReal_mul_I_re_eq_zero b)
    _ = a := by
      exact add_zero a

/-- Coordinates of the standard vertical parametrization: imaginary part. -/
private theorem complex_ofReal_add_ofReal_mul_I_im_eq
    (a b : ℝ) :
    (((a : ℝ) : ℂ) + ((b : ℝ) : ℂ) * Complex.I).im = b := by
  calc
    (((a : ℝ) : ℂ) + ((b : ℝ) : ℂ) * Complex.I).im =
        ((a : ℝ) : ℂ).im + (((b : ℝ) : ℂ) * Complex.I).im := by
      exact Complex.add_im ((a : ℝ) : ℂ) (((b : ℝ) : ℂ) * Complex.I)
    _ = 0 + (((b : ℝ) : ℂ) * Complex.I).im := by
      exact congrArg
        (fun x : ℝ => x + (((b : ℝ) : ℂ) * Complex.I).im)
        (Complex.ofReal_im a)
    _ = 0 + b := by
      exact congrArg (fun x : ℝ => 0 + x) (complex_ofReal_mul_I_im_eq b)
    _ = b := by
      exact zero_add b

/-- The real part of `1 - tI` is `1`. -/
private theorem complex_one_sub_ofReal_mul_I_re_eq_one
    (t : ℝ) :
    (((1 : ℂ) - (t : ℂ) * Complex.I).re) = 1 := by
  calc
    (((1 : ℂ) - (t : ℂ) * Complex.I).re) =
        (1 : ℂ).re - ((t : ℂ) * Complex.I).re := by
      exact Complex.sub_re (1 : ℂ) ((t : ℂ) * Complex.I)
    _ = 1 - ((t : ℂ) * Complex.I).re := by
      exact congrArg (fun x : ℝ => x - ((t : ℂ) * Complex.I).re) Complex.one_re
    _ = 1 - 0 := by
      exact congrArg (fun x : ℝ => 1 - x) (complex_ofReal_mul_I_re_eq_zero t)
    _ = 1 := by
      exact sub_zero 1

/-- The imaginary part of `1 - tI` is `-t`. -/
private theorem complex_one_sub_ofReal_mul_I_im_eq_neg
    (t : ℝ) :
    (((1 : ℂ) - (t : ℂ) * Complex.I).im) = -t := by
  calc
    (((1 : ℂ) - (t : ℂ) * Complex.I).im) =
        (1 : ℂ).im - ((t : ℂ) * Complex.I).im := by
      exact Complex.sub_im (1 : ℂ) ((t : ℂ) * Complex.I)
    _ = 0 - ((t : ℂ) * Complex.I).im := by
      exact congrArg (fun x : ℝ => x - ((t : ℂ) * Complex.I).im) Complex.one_im
    _ = 0 - t := by
      exact congrArg (fun x : ℝ => 0 - x) (complex_ofReal_mul_I_im_eq t)
    _ = -t := by
      exact zero_sub t

/-- The numerator Gamma argument on the left boundary is the fixed-real-part
vertical point `1/2 + i(-t/2)`. -/
theorem leftBoundary_numerator_complexGamma_argument_eq_fixedRealPart
    (t : ℝ) :
    (((1 : ℂ) - (t : ℂ) * Complex.I) / 2) =
      ((1 / 2 : ℝ) : ℂ) + ((-t / 2 : ℝ) : ℂ) * Complex.I := by
  have hre :
      ((((1 : ℂ) - (t : ℂ) * Complex.I) / 2)).re =
        (((1 / 2 : ℝ) : ℂ) + ((-t / 2 : ℝ) : ℂ) * Complex.I).re := by
    calc
      ((((1 : ℂ) - (t : ℂ) * Complex.I) / 2)).re =
          (((1 : ℂ) - (t : ℂ) * Complex.I).re) / 2 := by
        exact Complex.div_ofReal_re ((1 : ℂ) - (t : ℂ) * Complex.I) 2
      _ = 1 / 2 := by
        exact congrArg (fun x : ℝ => x / 2)
          (complex_one_sub_ofReal_mul_I_re_eq_one t)
      _ = (((1 / 2 : ℝ) : ℂ) + ((-t / 2 : ℝ) : ℂ) * Complex.I).re := by
        exact (complex_ofReal_add_ofReal_mul_I_re_eq (1 / 2) (-t / 2)).symm
  have him :
      ((((1 : ℂ) - (t : ℂ) * Complex.I) / 2)).im =
        (((1 / 2 : ℝ) : ℂ) + ((-t / 2 : ℝ) : ℂ) * Complex.I).im := by
    calc
      ((((1 : ℂ) - (t : ℂ) * Complex.I) / 2)).im =
          (((1 : ℂ) - (t : ℂ) * Complex.I).im) / 2 := by
        exact Complex.div_ofReal_im ((1 : ℂ) - (t : ℂ) * Complex.I) 2
      _ = -t / 2 := by
        exact congrArg (fun x : ℝ => x / 2)
          (complex_one_sub_ofReal_mul_I_im_eq_neg t)
      _ = (((1 / 2 : ℝ) : ℂ) + ((-t / 2 : ℝ) : ℂ) * Complex.I).im := by
        exact (complex_ofReal_add_ofReal_mul_I_im_eq (1 / 2) (-t / 2)).symm
  exact Complex.ext hre him

/-- The denominator Gamma argument on the left boundary is the fixed-real-part
vertical point `0 + i(t/2)`. -/
theorem leftBoundary_denominator_complexGamma_argument_eq_fixedRealPart
    (t : ℝ) :
    (((t : ℂ) * Complex.I) / 2) =
      ((0 : ℝ) : ℂ) + ((t / 2 : ℝ) : ℂ) * Complex.I := by
  have hre :
      (((t : ℂ) * Complex.I) / 2).re =
        (((0 : ℝ) : ℂ) + ((t / 2 : ℝ) : ℂ) * Complex.I).re := by
    calc
      (((t : ℂ) * Complex.I) / 2).re =
          (((t : ℂ) * Complex.I).re) / 2 := by
        exact Complex.div_ofReal_re ((t : ℂ) * Complex.I) 2
      _ = 0 := by
        exact Eq.subst
          (motive := fun x : ℝ => x / 2 = 0)
          (complex_ofReal_mul_I_re_eq_zero t).symm
          (zero_div (2 : ℝ))
      _ = (((0 : ℝ) : ℂ) + ((t / 2 : ℝ) : ℂ) * Complex.I).re := by
        exact (complex_ofReal_add_ofReal_mul_I_re_eq 0 (t / 2)).symm
  have him :
      (((t : ℂ) * Complex.I) / 2).im =
        (((0 : ℝ) : ℂ) + ((t / 2 : ℝ) : ℂ) * Complex.I).im := by
    calc
      (((t : ℂ) * Complex.I) / 2).im =
          (((t : ℂ) * Complex.I).im) / 2 := by
        exact Complex.div_ofReal_im ((t : ℂ) * Complex.I) 2
      _ = t / 2 := by
        exact congrArg (fun x : ℝ => x / 2) (complex_ofReal_mul_I_im_eq t)
      _ = (((0 : ℝ) : ℂ) + ((t / 2 : ℝ) : ℂ) * Complex.I).im := by
        exact (complex_ofReal_add_ofReal_mul_I_im_eq 0 (t / 2)).symm
  exact Complex.ext hre him

/-- The half-scaled vertical coordinate has norm at least `1/2` on the
left-boundary vertical-tail range. -/
theorem half_norm_ge_one_half_of_one_le_norm
    {t : ℝ}
    (ht : 1 ≤ ‖t‖) :
    (1 / 2 : ℝ) ≤ ‖t / 2‖ := by
  have htwo_pos : (0 : ℝ) < 2 := zero_lt_two
  have hnorm_div : ‖t / 2‖ = ‖t‖ / 2 := by
    calc
      ‖t / 2‖ = ‖t‖ / ‖(2 : ℝ)‖ := by
        exact norm_div t 2
      _ = ‖t‖ / 2 := by
        exact congrArg (fun x : ℝ => ‖t‖ / x)
          (Real.norm_of_nonneg (le_of_lt htwo_pos))
  exact Eq.subst
    (motive := fun x : ℝ => (1 / 2 : ℝ) ≤ x)
    hnorm_div.symm
    ((div_le_div_right htwo_pos).mpr ht)

/-- Negating the half-scaled vertical coordinate preserves the half-tail bound. -/
theorem neg_half_norm_ge_one_half_of_one_le_norm
    {t : ℝ}
    (ht : 1 ≤ ‖t‖) :
    (1 / 2 : ℝ) ≤ ‖-t / 2‖ := by
  have hneg_div : -t / 2 = -(t / 2) := by
    exact neg_div (2 : ℝ) t
  have hnorm : ‖-t / 2‖ = ‖t / 2‖ := by
    calc
      ‖-t / 2‖ = ‖-(t / 2)‖ := by
        exact congrArg norm hneg_div
      _ = ‖t / 2‖ :=
        norm_neg (t / 2)
  exact Eq.subst
    (motive := fun x : ℝ => (1 / 2 : ℝ) ≤ x)
    hnorm.symm
    (half_norm_ge_one_half_of_one_le_norm ht)

end
end LFunctions
end Boundary
