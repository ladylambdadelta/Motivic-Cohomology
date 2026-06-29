import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.GammaStirlingNormalization.BinetKernel.A_RealAnalysisBounds
import Mathlib

import Mathlib.Analysis.Complex.PhragmenLindelof
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.RCLike.Basic
import Mathlib.NumberTheory.AbelSummation
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Analysis.SpecialFunctions.Complex.Arctan
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Analysis.SpecialFunctions.Log.Monotone
import Mathlib.Data.Real.Pi.Bounds
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.SetIntegral
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.GammaBinetStirling.BinetAbelPlanaFiniteFormula
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.GammaBinetStirling.BinetTailContour
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.Core.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.FiniteOrderAlgebra.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.RightCriticalStripCompact.Owner

/-!
# Binet kernel and sectorial Gamma seed estimates

This file is a sequential owner sublayer split out of
`ZetaCompletedNormalization.GammaStirlingNormalization.Owner`.  Declaration order is preserved.
-/

namespace Boundary
namespace LFunctions

noncomputable section

theorem Complex.binetSecondFormula_logGamma_closedRightHalfPlane_largeRadius :
    ∃ R : ℝ,
      0 < R ∧
      ∀ w : ℂ,
        0 < w.re →
        R ≤ ‖w‖ →
        Complex.binetLogGammaBranch w =
          Complex.binetLogGammaMainTerm w +
            Complex.binetSecondFormulaRemainder w := by
  exact
    ⟨1, zero_lt_one,
      fun w _hw_re_pos _hw_norm =>
        Complex.binetLogGammaBranch_unfold w⟩

/-- Pointwise Binet-kernel estimate in the open right half-plane.

The numerator contributes the `t / ‖w‖` factor through the principal arctangent,
while the denominator is controlled by the positive real exponential
`exp (2πt) - 1`.  The open half-plane hypothesis avoids the principal
arctangent singularities on the imaginary boundary. -/
theorem Complex.norm_div_eq_div_norm
    {z w : ℂ}
    (hw : w ≠ 0) :
    ‖z / w‖ = ‖z‖ / ‖w‖ := by
  calc
    ‖z / w‖ = ‖z * w⁻¹‖ := by
      rfl
    _ = ‖z‖ * ‖w⁻¹‖ := norm_mul _ _
    _ = ‖z‖ * ‖w‖⁻¹ := by
      exact congrArg (fun x : ℝ => ‖z‖ * x) (norm_inv w)
    _ = ‖z‖ / ‖w‖ := by
      rfl

/-- `Complex.arctan` is a scalar multiple of the logarithmic quotient it is
defined from, in norm form. -/
theorem Complex.norm_arctan_le_abs_log_quotient_add_pi_half
    (z : ℂ)
    (hz : 1 - z * Complex.I ≠ 0) :
    ‖Complex.arctan z‖ ≤
      (|Real.log ((1 + z * Complex.I) / (1 - z * Complex.I)).abs| + π) / 2 := by
  have hlog := Complex.norm_log_le_abs_log_add_pi ((1 + z * Complex.I) / (1 - z * Complex.I))
  have hnorm := Complex.norm_arctan_eq_half_norm_log_quotient z hz
  have hhalf : ‖Complex.log ((1 + z * Complex.I) / (1 - z * Complex.I))‖ / 2 ≤
      (|Real.log ((1 + z * Complex.I) / (1 - z * Complex.I)).abs| + π) / 2 := by
    exact (div_le_div_iff_of_pos_right zero_lt_two).mpr hlog
  calc
    ‖Complex.arctan z‖ = ‖Complex.log ((1 + z * Complex.I) / (1 - z * Complex.I))‖ / 2 := hnorm
    _ ≤ (|Real.log ((1 + z * Complex.I) / (1 - z * Complex.I)).abs| + π) / 2 := hhalf

/-- The argument of the Binet quotient is always within `[-π, π]`. -/
theorem Complex.arg_binet_quotient_le_pi
    (z : ℂ) :
    |Complex.arg ((1 + z * Complex.I) / (1 - z * Complex.I))| ≤ π := by
  exact Complex.abs_arg_le_pi _

/-- The Binet quotient log norm is controlled by its real part and the
universal `π` argument bound. -/
theorem Complex.log_binet_quotient_re_eq_log_ratio (z : ℂ)
    (h1 : 1 + z * Complex.I ≠ 0) (h2 : 1 - z * Complex.I ≠ 0) :
    (Complex.log ((1 + z * Complex.I) / (1 - z * Complex.I))).re =
      Real.log ‖1 + z * Complex.I‖ - Real.log ‖1 - z * Complex.I‖ := by
  calc
    (Complex.log ((1 + z * Complex.I) / (1 - z * Complex.I))).re =
        Real.log ‖(1 + z * Complex.I) / (1 - z * Complex.I)‖ := Complex.log_re _
    _ = Real.log (‖1 + z * Complex.I‖ / ‖1 - z * Complex.I‖) := by
      exact congrArg Real.log (Complex.norm_div_eq_div_norm h2)
    _ = Real.log ‖1 + z * Complex.I‖ - Real.log ‖1 - z * Complex.I‖ := by
      exact Real.log_div (norm_ne_zero_iff.mpr h1) (norm_ne_zero_iff.mpr h2)

/-- The imaginary part of the Binet quotient logarithm is its argument. -/
theorem Complex.log_binet_quotient_im_eq_arg_ratio (z : ℂ) :
    (Complex.log ((1 + z * Complex.I) / (1 - z * Complex.I))).im =
      Complex.arg ((1 + z * Complex.I) / (1 - z * Complex.I)) := by
  exact Complex.log_im _

/-- The Binet quotient logarithm is exactly the pair of its real and imaginary
coordinate formulas. -/
theorem Complex.log_binet_quotient_coords (z : ℂ)
    (h1 : 1 + z * Complex.I ≠ 0) (h2 : 1 - z * Complex.I ≠ 0) :
    Complex.log ((1 + z * Complex.I) / (1 - z * Complex.I)) =
      (Real.log ‖1 + z * Complex.I‖ - Real.log ‖1 - z * Complex.I‖) +
        Complex.arg ((1 + z * Complex.I) / (1 - z * Complex.I)) * Complex.I := by
  let q : ℂ := (1 + z * Complex.I) / (1 - z * Complex.I)
  have hsplit : Complex.log q = ((Complex.log q).re : ℂ) + (Complex.log q).im * Complex.I :=
    (Complex.re_add_im (Complex.log q)).symm
  have hre :
      ((Complex.log q).re : ℂ) =
        (Real.log ‖1 + z * Complex.I‖ - Real.log ‖1 - z * Complex.I‖ : ℂ) := by
    have hre_real :
        (Complex.log q).re =
          Real.log ‖1 + z * Complex.I‖ - Real.log ‖1 - z * Complex.I‖ :=
      Complex.log_binet_quotient_re_eq_log_ratio z h1 h2
    calc
      ((Complex.log q).re : ℂ) =
          ((Real.log ‖1 + z * Complex.I‖ -
            Real.log ‖1 - z * Complex.I‖ : ℝ) : ℂ) :=
        congrArg (fun x : ℝ => (x : ℂ)) hre_real
      _ =
          (Real.log ‖1 + z * Complex.I‖ : ℂ) -
            (Real.log ‖1 - z * Complex.I‖ : ℂ) :=
        Complex.ofReal_sub
          (Real.log ‖1 + z * Complex.I‖)
          (Real.log ‖1 - z * Complex.I‖)
  have him :
      (Complex.log q).im * Complex.I =
        Complex.arg q * Complex.I := by
    exact congrArg (fun x : ℝ => (x : ℂ) * Complex.I)
      (Complex.log_binet_quotient_im_eq_arg_ratio z)
  calc
    Complex.log ((1 + z * Complex.I) / (1 - z * Complex.I)) =
        Complex.log q := rfl
    _ = ((Complex.log q).re : ℂ) + (Complex.log q).im * Complex.I := hsplit
    _ = (Real.log ‖1 + z * Complex.I‖ - Real.log ‖1 - z * Complex.I‖ : ℂ) +
        Complex.arg q * Complex.I := congrArg₂ HAdd.hAdd hre him
    _ =
        (Real.log ‖1 + z * Complex.I‖ - Real.log ‖1 - z * Complex.I‖) +
          Complex.arg ((1 + z * Complex.I) / (1 - z * Complex.I)) * Complex.I := rfl

/-- The Binet quotient logarithm has real and imaginary parts given by the
coordinate formulas. -/
theorem Complex.log_binet_quotient_re_im (z : ℂ)
    (h1 : 1 + z * Complex.I ≠ 0) (h2 : 1 - z * Complex.I ≠ 0) :
    (Complex.log ((1 + z * Complex.I) / (1 - z * Complex.I))).re =
      Real.log ‖1 + z * Complex.I‖ - Real.log ‖1 - z * Complex.I‖ ∧
    (Complex.log ((1 + z * Complex.I) / (1 - z * Complex.I))).im =
      Complex.arg ((1 + z * Complex.I) / (1 - z * Complex.I)) := by
  exact
    ⟨
      (Complex.log_binet_quotient_re_eq_log_ratio z h1 h2),
      (Complex.log_binet_quotient_im_eq_arg_ratio z)⟩

/-- The Binet quotient factors are both nonzero whenever z has nonzero real part.

The imaginary part of `1 + z * I` equals `z.re`, and the imaginary part of
`1 - z * I` equals `-z.re`.  If either factor were zero its imaginary part
would be zero, forcing `z.re = 0`. -/
theorem Complex.binet_quotient_factors_ne_zero
    (z : ℂ)
    (hz : z.re ≠ 0) :
    1 + z * Complex.I ≠ 0 ∧ 1 - z * Complex.I ≠ 0 :=
  ⟨fun h1 =>
    let him_plus : (1 + z * Complex.I).im = z.re :=
      calc (1 + z * Complex.I).im
          = (1 : ℂ).im + (z * Complex.I).im :=
            Complex.add_im 1 (z * Complex.I)
        _ = 0 + (z * Complex.I).im :=
            congrArg (fun x : ℝ => x + (z * Complex.I).im) Complex.one_im
        _ = (z * Complex.I).im :=
            zero_add (z * Complex.I).im
        _ = z.re * Complex.I.im + z.im * Complex.I.re :=
            Complex.mul_im z Complex.I
        _ = z.re * 1 + z.im * 0 :=
            congrArg₂ (fun a b : ℝ => z.re * a + z.im * b) Complex.I_im Complex.I_re
        _ = z.re + 0 :=
            congrArg₂ (fun a b : ℝ => a + b) (mul_one z.re) (mul_zero z.im)
        _ = z.re :=
            add_zero z.re
    let him_zero : (1 + z * Complex.I).im = 0 :=
      (congrArg Complex.im h1).trans Complex.zero_im
    hz (him_plus.symm.trans him_zero),
  fun h2 =>
    let him_minus : (1 - z * Complex.I).im = -z.re :=
      calc (1 - z * Complex.I).im
          = (1 : ℂ).im - (z * Complex.I).im :=
            Complex.sub_im 1 (z * Complex.I)
        _ = 0 - (z * Complex.I).im :=
            congrArg (fun x : ℝ => x - (z * Complex.I).im) Complex.one_im
        _ = -(z * Complex.I).im :=
            zero_sub (z * Complex.I).im
        _ = -(z.re * Complex.I.im + z.im * Complex.I.re) :=
            congrArg Neg.neg (Complex.mul_im z Complex.I)
        _ = -(z.re * 1 + z.im * 0) :=
            congrArg (fun x : ℝ => -x)
              (congrArg₂ (fun a b : ℝ => z.re * a + z.im * b) Complex.I_im Complex.I_re)
        _ = -(z.re + 0) :=
            congrArg (fun x : ℝ => -x)
              (congrArg₂ (fun a b : ℝ => a + b) (mul_one z.re) (mul_zero z.im))
        _ = -z.re :=
            congrArg Neg.neg (add_zero z.re)
    let him_zero : (1 - z * Complex.I).im = 0 :=
      (congrArg Complex.im h2).trans Complex.zero_im
    hz (neg_eq_zero.mp (him_minus.symm.trans him_zero))⟩

/-- The Binet plus factor is nonzero whenever z has nonzero real part. -/
theorem Complex.binet_quotient_factors_ne_zero_of_re_ne_zero
    (z : ℂ)
    (hz : z.re ≠ 0) :
    1 + z * Complex.I ≠ 0 :=
  (Complex.binet_quotient_factors_ne_zero z hz).1

/-- The Binet quotient factors are both nonzero whenever the real part is
nonzero.  This replaces the earlier false statement which claimed to derive
numerator nonvanishing from denominator nonvanishing alone. -/
theorem Complex.binet_quotient_factors_ne_zero_of_denominator_ne_zero
    (z : ℂ)
    (hz : z.re ≠ 0) :
    1 + z * Complex.I ≠ 0 :=
  Complex.binet_quotient_factors_ne_zero_of_re_ne_zero z hz

/-- Small-argument Binet remainder estimate with the explicit `1 / ‖w‖`
factor. -/


end
end LFunctions
end Boundary
