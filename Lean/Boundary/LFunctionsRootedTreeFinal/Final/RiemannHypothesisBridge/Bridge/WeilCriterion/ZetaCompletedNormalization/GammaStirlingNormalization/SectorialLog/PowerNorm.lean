import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.GammaStirlingNormalization.SectorialLog.Envelope
import Mathlib.Analysis.SpecialFunctions.Pow.Complex

/-!
# Sectorial log: elementary exponential and power norm identities

This subowner contains the branch-independent norm identities needed to expand
the normalized Stirling denominator.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped Filter Topology
local notation "π" => Real.pi

/-- The real half embedded in `ℂ` is the complex half. -/
theorem Complex.ofReal_one_div_two_eq_complex_one_div_two :
    (((1 / 2 : ℝ) : ℂ) = (1 / 2 : ℂ)) := by
  exact Complex.ofReal_div 1 2

/-- Norm of the complex exponential. -/
theorem Complex.norm_exp_eq_exp_re
    (w : ℂ) :
    ‖Complex.exp w‖ = Real.exp w.re := by
  have hnorm_eq_abs :
      ‖Complex.exp w‖ = Complex.abs (Complex.exp w) :=
    Complex.norm_eq_abs (Complex.exp w)
  calc
    ‖Complex.exp w‖ = Complex.abs (Complex.exp w) :=
      hnorm_eq_abs
    _ = Real.exp w.re :=
      Complex.abs_exp w

/-- Principal-branch norm formula for complex powers. -/
theorem Complex.norm_cpow_eq_norm_rpow_div_exp_arg_mul_im_of_ne_zero
    {z a : ℂ}
    (hz_ne : z ≠ 0) :
    ‖z ^ a‖ =
      ‖z‖ ^ a.re / Real.exp (Complex.arg z * a.im) := by
  have hnorm_cpow_abs :
      ‖z ^ a‖ = Complex.abs (z ^ a) :=
    Complex.norm_eq_abs (z ^ a)
  have hnorm_z_abs :
      ‖z‖ = Complex.abs z :=
    Complex.norm_eq_abs z
  have habs_cpow :
      Complex.abs (z ^ a) =
        Complex.abs z ^ a.re / Real.exp (Complex.arg z * a.im) :=
    Complex.abs_cpow_of_ne_zero hz_ne a
  calc
    ‖z ^ a‖ = Complex.abs (z ^ a) :=
      hnorm_cpow_abs
    _ = Complex.abs z ^ a.re / Real.exp (Complex.arg z * a.im) :=
      habs_cpow
    _ = ‖z‖ ^ a.re / Real.exp (Complex.arg z * a.im) := by
      exact congrArg
        (fun r : ℝ => r ^ a.re / Real.exp (Complex.arg z * a.im))
        hnorm_z_abs.symm

/-- Real coordinate of the Stirling power exponent `(1/2) - w`. -/
theorem Complex.half_minus_self_re
    (w : ℂ) :
    ((1 / 2 : ℂ) - w).re = (1 / 2 : ℝ) - w.re := by
  calc
    ((1 / 2 : ℂ) - w).re =
        (1 / 2 : ℂ).re - w.re :=
      Complex.sub_re (1 / 2 : ℂ) w
    _ = (((1 / 2 : ℝ) : ℂ).re) - w.re := by
      exact congrArg
        (fun z : ℂ => z.re - w.re)
        Complex.ofReal_one_div_two_eq_complex_one_div_two.symm
    _ = (1 / 2 : ℝ) - w.re := by
      exact congrArg (fun x : ℝ => x - w.re) (Complex.ofReal_re (1 / 2 : ℝ))

/-- Imaginary coordinate of the Stirling power exponent `(1/2) - w`. -/
theorem Complex.half_minus_self_im
    (w : ℂ) :
    ((1 / 2 : ℂ) - w).im = -w.im := by
  calc
    ((1 / 2 : ℂ) - w).im =
        (1 / 2 : ℂ).im - w.im :=
      Complex.sub_im (1 / 2 : ℂ) w
    _ = (((1 / 2 : ℝ) : ℂ).im) - w.im := by
      exact congrArg
        (fun z : ℂ => z.im - w.im)
        Complex.ofReal_one_div_two_eq_complex_one_div_two.symm
    _ = 0 - w.im := by
      exact congrArg (fun x : ℝ => x - w.im) (Complex.ofReal_im (1 / 2 : ℝ))
    _ = -w.im :=
      zero_sub w.im

end

end LFunctions
end Boundary
