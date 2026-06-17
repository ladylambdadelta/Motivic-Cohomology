import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.ZetaEulerMaclaurinBoundary.LogarithmicPhase.RealPhaseBasics
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.ZetaEulerMaclaurinBoundary.LogarithmicPhase.AbelCore
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Angle
import Mathlib.Data.Complex.ExponentialBounds
import Mathlib.Data.Rat.Cast.Order

/-!
# Logarithmic phase estimates

This file owns the oscillatory phase `n^{-it}` input used by the
Euler-Maclaurin boundary argument.  The phase is logarithmic, not a
constant-ratio geometric progression.
-/

namespace Boundary
namespace LFunctions

noncomputable section

/-- The real half embedded in `ℂ` is the complex half. -/
theorem Complex.ofReal_one_div_two_eq_complex_one_div_two :
    (((1 / 2 : ℝ) : ℂ) = (1 / 2 : ℂ)) := by
  exact Complex.ofReal_div 1 2

/-- The inverse chord map on the reduced logarithmic-phase arc. -/
def Complex.reducedArc_inverseGeometricDenominator
    (ψ : ℝ) : ℂ :=
  (1 - Complex.exp (Complex.I * (ψ : ℂ)))⁻¹

/-- Definitional expansion of the reduced-arc inverse chord map. -/
theorem Complex.reducedArc_inverseGeometricDenominator_eq
    (ψ : ℝ) :
    Complex.reducedArc_inverseGeometricDenominator ψ =
      (1 - Complex.exp (Complex.I * (ψ : ℂ)))⁻¹ := by
  rfl

/-- The real coordinate of the inverse chord map on a reduced arc. -/
def Complex.reducedArc_inverseGeometricDenominator_imCoord
    (ψ : ℝ) : ℝ :=
  (Complex.reducedArc_inverseGeometricDenominator ψ).im

/-- The real coordinate of a point written as `1 / 2 + I * y`. -/
theorem Complex.half_add_I_mul_ofReal_re
    (y : ℝ) :
    ((((1 / 2 : ℝ) : ℂ) + Complex.I * (y : ℂ)).re) = 1 / 2 := by
  have himaginary_re :
      (Complex.I * (y : ℂ)).re = 0 := by
    have hmul :
        (Complex.I * (y : ℂ)).re = (-(y : ℂ).im) :=
      congrArg Complex.re (Complex.I_mul (y : ℂ))
    exact Eq.trans hmul (neg_eq_zero.mpr (Complex.ofReal_im y))
  calc
    ((((1 / 2 : ℝ) : ℂ) + Complex.I * (y : ℂ)).re) =
        (((1 / 2 : ℝ) : ℂ).re) + (Complex.I * (y : ℂ)).re :=
      Complex.add_re ((1 / 2 : ℝ) : ℂ) (Complex.I * (y : ℂ))
    _ = (1 / 2 : ℝ) + (Complex.I * (y : ℂ)).re := by
      exact congrArg
        (fun x : ℝ => x + (Complex.I * (y : ℂ)).re)
        (Complex.ofReal_re (1 / 2 : ℝ))
    _ = (1 / 2 : ℝ) + 0 := by
      exact congrArg (fun x : ℝ => (1 / 2 : ℝ) + x) himaginary_re
    _ = 1 / 2 :=
      add_zero (1 / 2 : ℝ)

/-- The imaginary coordinate of a point written as `1 / 2 + I * y`. -/
theorem Complex.half_add_I_mul_ofReal_im
    (y : ℝ) :
    ((((1 / 2 : ℝ) : ℂ) + Complex.I * (y : ℂ)).im) = y := by
  have hreal_im :
      (((1 / 2 : ℝ) : ℂ).im) = 0 :=
    Complex.ofReal_im (1 / 2 : ℝ)
  have himaginary_im :
      (Complex.I * (y : ℂ)).im = y := by
    have hmul :
        (Complex.I * (y : ℂ)).im = (y : ℂ).re :=
      congrArg Complex.im (Complex.I_mul (y : ℂ))
    exact Eq.trans hmul (Complex.ofReal_re y)
  calc
    ((((1 / 2 : ℝ) : ℂ) + Complex.I * (y : ℂ)).im) =
        (((1 / 2 : ℝ) : ℂ).im) + (Complex.I * (y : ℂ)).im :=
      Complex.add_im ((1 / 2 : ℝ) : ℂ) (Complex.I * (y : ℂ))
    _ = 0 + (Complex.I * (y : ℂ)).im := by
      exact congrArg
        (fun x : ℝ => x + (Complex.I * (y : ℂ)).im)
        hreal_im
    _ = 0 + y := by
      exact congrArg (fun x : ℝ => 0 + x) himaginary_im
    _ = y :=
      zero_add y

/-- Real-coordinate subtraction on the vertical line `1 / 2 + I * ℝ`. -/
theorem Complex.half_add_I_mul_ofReal_sub_re
    (x y : ℝ) :
    ((((1 / 2 : ℝ) : ℂ) + Complex.I * (x : ℂ)) -
        (((1 / 2 : ℝ) : ℂ) + Complex.I * (y : ℂ))).re =
      (Complex.I * ((x - y : ℝ) : ℂ)).re := by
  have hleft_first :
      (((1 / 2 : ℝ) : ℂ) + Complex.I * (x : ℂ)).re = 1 / 2 := by
    calc
      (((1 / 2 : ℝ) : ℂ) + Complex.I * (x : ℂ)).re =
          (((1 / 2 : ℝ) : ℂ).re) + (Complex.I * (x : ℂ)).re :=
        Complex.add_re (((1 / 2 : ℝ) : ℂ)) (Complex.I * (x : ℂ))
      _ = (1 / 2 : ℝ) + (Complex.I * (x : ℂ)).re := by
        exact congrArg
          (fun r : ℝ => r + (Complex.I * (x : ℂ)).re)
          (Complex.ofReal_re (1 / 2 : ℝ))
      _ = (1 / 2 : ℝ) + (-(x : ℂ).im) := by
        exact congrArg
          (fun r : ℝ => (1 / 2 : ℝ) + r)
          (Complex.I_mul_re (x : ℂ))
      _ = (1 / 2 : ℝ) + (-0) := by
        exact congrArg
          (fun r : ℝ => (1 / 2 : ℝ) + (-r))
          (Complex.ofReal_im x)
      _ = (1 / 2 : ℝ) + 0 := by
        exact congrArg
          (fun r : ℝ => (1 / 2 : ℝ) + r)
          (neg_zero : -(0 : ℝ) = 0)
      _ = 1 / 2 :=
        add_zero (1 / 2 : ℝ)
  have hleft_second :
      (((1 / 2 : ℝ) : ℂ) + Complex.I * (y : ℂ)).re = 1 / 2 := by
    calc
      (((1 / 2 : ℝ) : ℂ) + Complex.I * (y : ℂ)).re =
          (((1 / 2 : ℝ) : ℂ).re) + (Complex.I * (y : ℂ)).re :=
        Complex.add_re (((1 / 2 : ℝ) : ℂ)) (Complex.I * (y : ℂ))
      _ = (1 / 2 : ℝ) + (Complex.I * (y : ℂ)).re := by
        exact congrArg
          (fun r : ℝ => r + (Complex.I * (y : ℂ)).re)
          (Complex.ofReal_re (1 / 2 : ℝ))
      _ = (1 / 2 : ℝ) + (-(y : ℂ).im) := by
        exact congrArg
          (fun r : ℝ => (1 / 2 : ℝ) + r)
          (Complex.I_mul_re (y : ℂ))
      _ = (1 / 2 : ℝ) + (-0) := by
        exact congrArg
          (fun r : ℝ => (1 / 2 : ℝ) + (-r))
          (Complex.ofReal_im y)
      _ = (1 / 2 : ℝ) + 0 := by
        exact congrArg
          (fun r : ℝ => (1 / 2 : ℝ) + r)
          (neg_zero : -(0 : ℝ) = 0)
      _ = 1 / 2 :=
        add_zero (1 / 2 : ℝ)
  have hright :
      (Complex.I * ((x - y : ℝ) : ℂ)).re = 0 := by
    calc
      (Complex.I * ((x - y : ℝ) : ℂ)).re =
          (-(((x - y : ℝ) : ℂ).im)) :=
        Complex.I_mul_re (((x - y : ℝ) : ℂ))
      _ = -0 := by
        exact congrArg Neg.neg (Complex.ofReal_im (x - y))
      _ = 0 :=
        neg_zero
  calc
    ((((1 / 2 : ℝ) : ℂ) + Complex.I * (x : ℂ)) -
        (((1 / 2 : ℝ) : ℂ) + Complex.I * (y : ℂ))).re =
        (((1 / 2 : ℝ) : ℂ) + Complex.I * (x : ℂ)).re -
          (((1 / 2 : ℝ) : ℂ) + Complex.I * (y : ℂ)).re :=
      Complex.sub_re
        (((1 / 2 : ℝ) : ℂ) + Complex.I * (x : ℂ))
        (((1 / 2 : ℝ) : ℂ) + Complex.I * (y : ℂ))
    _ = (1 / 2 : ℝ) - (1 / 2 : ℝ) := by
      exact congrArg₂ Sub.sub hleft_first hleft_second
    _ = 0 := by
      exact sub_self (1 / 2 : ℝ)
    _ = (Complex.I * ((x - y : ℝ) : ℂ)).re :=
      hright.symm

/-- Imaginary-coordinate subtraction on the vertical line `1 / 2 + I * ℝ`. -/
theorem Complex.half_add_I_mul_ofReal_sub_im
    (x y : ℝ) :
    ((((1 / 2 : ℝ) : ℂ) + Complex.I * (x : ℂ)) -
        (((1 / 2 : ℝ) : ℂ) + Complex.I * (y : ℂ))).im =
      (Complex.I * ((x - y : ℝ) : ℂ)).im := by
  have hleft_first :
      (((1 / 2 : ℝ) : ℂ) + Complex.I * (x : ℂ)).im = x := by
    calc
      (((1 / 2 : ℝ) : ℂ) + Complex.I * (x : ℂ)).im =
          (((1 / 2 : ℝ) : ℂ).im) + (Complex.I * (x : ℂ)).im :=
        Complex.add_im (((1 / 2 : ℝ) : ℂ)) (Complex.I * (x : ℂ))
      _ = 0 + (Complex.I * (x : ℂ)).im := by
        exact congrArg
          (fun r : ℝ => r + (Complex.I * (x : ℂ)).im)
          (Complex.ofReal_im (1 / 2 : ℝ))
      _ = 0 + (x : ℂ).re := by
        exact congrArg
          (fun r : ℝ => 0 + r)
          (Complex.I_mul_im (x : ℂ))
      _ = 0 + x := by
        exact congrArg (fun r : ℝ => 0 + r) (Complex.ofReal_re x)
      _ = x :=
        zero_add x
  have hleft_second :
      (((1 / 2 : ℝ) : ℂ) + Complex.I * (y : ℂ)).im = y := by
    calc
      (((1 / 2 : ℝ) : ℂ) + Complex.I * (y : ℂ)).im =
          (((1 / 2 : ℝ) : ℂ).im) + (Complex.I * (y : ℂ)).im :=
        Complex.add_im (((1 / 2 : ℝ) : ℂ)) (Complex.I * (y : ℂ))
      _ = 0 + (Complex.I * (y : ℂ)).im := by
        exact congrArg
          (fun r : ℝ => r + (Complex.I * (y : ℂ)).im)
          (Complex.ofReal_im (1 / 2 : ℝ))
      _ = 0 + (y : ℂ).re := by
        exact congrArg
          (fun r : ℝ => 0 + r)
          (Complex.I_mul_im (y : ℂ))
      _ = 0 + y := by
        exact congrArg (fun r : ℝ => 0 + r) (Complex.ofReal_re y)
      _ = y :=
        zero_add y
  have hright :
      (Complex.I * ((x - y : ℝ) : ℂ)).im = x - y := by
    calc
      (Complex.I * ((x - y : ℝ) : ℂ)).im =
          (((x - y : ℝ) : ℂ).re) :=
        Complex.I_mul_im (((x - y : ℝ) : ℂ))
      _ = x - y :=
        Complex.ofReal_re (x - y)
  calc
    ((((1 / 2 : ℝ) : ℂ) + Complex.I * (x : ℂ)) -
        (((1 / 2 : ℝ) : ℂ) + Complex.I * (y : ℂ))).im =
        (((1 / 2 : ℝ) : ℂ) + Complex.I * (x : ℂ)).im -
          (((1 / 2 : ℝ) : ℂ) + Complex.I * (y : ℂ)).im :=
      Complex.sub_im
        (((1 / 2 : ℝ) : ℂ) + Complex.I * (x : ℂ))
        (((1 / 2 : ℝ) : ℂ) + Complex.I * (y : ℂ))
    _ = x - y := by
      exact congrArg₂ Sub.sub hleft_first hleft_second
    _ = (Complex.I * ((x - y : ℝ) : ℂ)).im :=
      hright.symm

/-- Subtracting two points on the vertical line `1 / 2 + I * ℝ`. -/
theorem Complex.half_add_I_mul_ofReal_sub
    (x y : ℝ) :
    (((1 / 2 : ℝ) : ℂ) + Complex.I * (x : ℂ)) -
        (((1 / 2 : ℝ) : ℂ) + Complex.I * (y : ℂ)) =
      Complex.I * ((x - y : ℝ) : ℂ) := by
  exact Complex.ext
    (Complex.half_add_I_mul_ofReal_sub_re x y)
    (Complex.half_add_I_mul_ofReal_sub_im x y)

/-- Subtracting two points on the vertical line in complex-half normal form. -/
theorem Complex.half_add_I_mul_ofReal_sub_complexHalf
    (x y : ℝ) :
    (1 / 2 : ℂ) + Complex.I * (x : ℂ) -
        ((1 / 2 : ℂ) + Complex.I * (y : ℂ)) =
      Complex.I * ((x - y : ℝ) : ℂ) := by
  have hleft :
      (1 / 2 : ℂ) + Complex.I * (x : ℂ) =
        ((1 / 2 : ℝ) : ℂ) + Complex.I * (x : ℂ) := by
    exact congrArg (fun q : ℂ => q + Complex.I * (x : ℂ))
      Complex.ofReal_one_div_two_eq_complex_one_div_two.symm
  have hright :
      (1 / 2 : ℂ) + Complex.I * (y : ℂ) =
        ((1 / 2 : ℝ) : ℂ) + Complex.I * (y : ℂ) := by
    exact congrArg (fun q : ℂ => q + Complex.I * (y : ℂ))
      Complex.ofReal_one_div_two_eq_complex_one_div_two.symm
  exact Eq.trans
    (congrArg₂ Sub.sub hleft hright)
    (Complex.half_add_I_mul_ofReal_sub x y)

/-- The reduced arc lies inside the lower endpoint range for the standard
`cos = 1` criterion. -/
theorem Real.reducedArc_gt_neg_two_pi
    {ψ : ℝ}
    (hψ_mem : ψ ∈ Set.Ioc (-Real.pi) Real.pi) :
    -(2 * Real.pi) < ψ := by
  have hneg_pi_lt : -Real.pi < ψ :=
    hψ_mem.1
  have hpi_pos : 0 < Real.pi :=
    Real.pi_pos
  have hpi_lt_two_pi : Real.pi < 2 * Real.pi := by
    exact lt_two_mul_self hpi_pos
  have hneg_two_pi_lt_neg_pi : -(2 * Real.pi) < -Real.pi :=
    neg_lt_neg hpi_lt_two_pi
  exact lt_trans hneg_two_pi_lt_neg_pi hneg_pi_lt

/-- The reduced arc lies inside the upper endpoint range for the standard
`cos = 1` criterion. -/
theorem Real.reducedArc_lt_two_pi
    {ψ : ℝ}
    (hψ_mem : ψ ∈ Set.Ioc (-Real.pi) Real.pi) :
    ψ < 2 * Real.pi := by
  have hψ_le_pi : ψ ≤ Real.pi :=
    hψ_mem.2
  have hpi_pos : 0 < Real.pi :=
    Real.pi_pos
  have hpi_lt_two_pi : Real.pi < 2 * Real.pi := by
    exact lt_two_mul_self hpi_pos
  exact lt_of_le_of_lt hψ_le_pi hpi_lt_two_pi

/-- On the punctured reduced arc, `1 - cos ψ` is nonzero. -/
theorem Real.one_sub_cos_ne_zero_of_mem_reducedArc
    {ψ : ℝ}
    (hψ_mem : ψ ∈ Set.Ioc (-Real.pi) Real.pi)
    (hψ_ne : ψ ≠ 0) :
    1 - Real.cos ψ ≠ 0 := by
  have hψ_gt_neg_two_pi : -(2 * Real.pi) < ψ :=
    Real.reducedArc_gt_neg_two_pi hψ_mem
  have hψ_lt_two_pi : ψ < 2 * Real.pi :=
    Real.reducedArc_lt_two_pi hψ_mem
  intro hzero
  have hcos : Real.cos ψ = 1 :=
    (sub_eq_zero.mp hzero).symm
  have hψ_zero : ψ = 0 :=
    (Real.cos_eq_one_iff_of_lt_of_lt hψ_gt_neg_two_pi hψ_lt_two_pi).mp hcos
  exact hψ_ne hψ_zero

/-- The denominator in the inverse-chord imaginary coordinate is nonzero on the
punctured reduced arc. -/
theorem Real.two_mul_one_sub_cos_ne_zero_of_mem_reducedArc
    {ψ : ℝ}
    (hψ_mem : ψ ∈ Set.Ioc (-Real.pi) Real.pi)
    (hψ_ne : ψ ≠ 0) :
    2 * (1 - Real.cos ψ) ≠ 0 := by
  have htwo_ne : (2 : ℝ) ≠ 0 :=
    two_ne_zero
  have hone_sub_cos_ne : 1 - Real.cos ψ ≠ 0 :=
    Real.one_sub_cos_ne_zero_of_mem_reducedArc hψ_mem hψ_ne
  exact mul_ne_zero htwo_ne hone_sub_cos_ne

/-- Real coordinate of the elementary chord denominator written in trigonometric
coordinates. -/
theorem Complex.one_sub_cos_add_sin_mul_I_re
    (c s : ℝ) :
    (1 - ((c : ℂ) + (s : ℂ) * Complex.I)).re = 1 - c := by
  have hmul_re :
      ((s : ℂ) * Complex.I).re = 0 := by
    calc
      ((s : ℂ) * Complex.I).re =
          (s : ℂ).re * Complex.I.re - (s : ℂ).im * Complex.I.im :=
        Complex.mul_re (s : ℂ) Complex.I
      _ = s * Complex.I.re - (s : ℂ).im * Complex.I.im := by
        exact congrArg
          (fun r : ℝ => r * Complex.I.re - (s : ℂ).im * Complex.I.im)
          (Complex.ofReal_re s)
      _ = s * 0 - (s : ℂ).im * Complex.I.im := by
        exact congrArg
          (fun r : ℝ => s * r - (s : ℂ).im * Complex.I.im)
          Complex.I_re
      _ = 0 - (s : ℂ).im * Complex.I.im := by
        exact congrArg
          (fun r : ℝ => r - (s : ℂ).im * Complex.I.im)
          (mul_zero s)
      _ = 0 - 0 * Complex.I.im := by
        exact congrArg
          (fun r : ℝ => 0 - r * Complex.I.im)
          (Complex.ofReal_im s)
      _ = 0 - 0 := by
        exact congrArg (fun r : ℝ => 0 - r) (zero_mul Complex.I.im)
      _ = 0 :=
        sub_self 0
  have hadd_re :
      (((c : ℂ) + (s : ℂ) * Complex.I).re) = c := by
    calc
      (((c : ℂ) + (s : ℂ) * Complex.I).re) =
          (c : ℂ).re + ((s : ℂ) * Complex.I).re :=
        Complex.add_re (c : ℂ) ((s : ℂ) * Complex.I)
      _ = c + ((s : ℂ) * Complex.I).re := by
        exact congrArg
          (fun r : ℝ => r + ((s : ℂ) * Complex.I).re)
          (Complex.ofReal_re c)
      _ = c + 0 := by
        exact congrArg (fun r : ℝ => c + r) hmul_re
      _ = c :=
        add_zero c
  calc
    (1 - ((c : ℂ) + (s : ℂ) * Complex.I)).re =
        (1 : ℂ).re - ((c : ℂ) + (s : ℂ) * Complex.I).re :=
      Complex.sub_re (1 : ℂ) ((c : ℂ) + (s : ℂ) * Complex.I)
    _ = 1 - ((c : ℂ) + (s : ℂ) * Complex.I).re := by
      exact congrArg
        (fun r : ℝ => r - ((c : ℂ) + (s : ℂ) * Complex.I).re)
        Complex.one_re
    _ = 1 - c := by
      exact congrArg (fun r : ℝ => 1 - r) hadd_re

/-- Imaginary coordinate of the elementary chord denominator written in
trigonometric coordinates. -/
theorem Complex.one_sub_cos_add_sin_mul_I_im
    (c s : ℝ) :
    (1 - ((c : ℂ) + (s : ℂ) * Complex.I)).im = -s := by
  have hmul_im :
      ((s : ℂ) * Complex.I).im = s := by
    calc
      ((s : ℂ) * Complex.I).im =
          (s : ℂ).re * Complex.I.im + (s : ℂ).im * Complex.I.re :=
        Complex.mul_im (s : ℂ) Complex.I
      _ = s * Complex.I.im + (s : ℂ).im * Complex.I.re := by
        exact congrArg
          (fun r : ℝ => r * Complex.I.im + (s : ℂ).im * Complex.I.re)
          (Complex.ofReal_re s)
      _ = s * 1 + (s : ℂ).im * Complex.I.re := by
        exact congrArg
          (fun r : ℝ => s * r + (s : ℂ).im * Complex.I.re)
          Complex.I_im
      _ = s * 1 + 0 * Complex.I.re := by
        exact congrArg
          (fun r : ℝ => s * 1 + r * Complex.I.re)
          (Complex.ofReal_im s)
      _ = s + 0 * Complex.I.re := by
        exact congrArg (fun r : ℝ => r + 0 * Complex.I.re) (mul_one s)
      _ = s + 0 := by
        exact congrArg (fun r : ℝ => s + r) (zero_mul Complex.I.re)
      _ = s :=
        add_zero s
  have hadd_im :
      (((c : ℂ) + (s : ℂ) * Complex.I).im) = s := by
    calc
      (((c : ℂ) + (s : ℂ) * Complex.I).im) =
          (c : ℂ).im + ((s : ℂ) * Complex.I).im :=
        Complex.add_im (c : ℂ) ((s : ℂ) * Complex.I)
      _ = 0 + ((s : ℂ) * Complex.I).im := by
        exact congrArg
          (fun r : ℝ => r + ((s : ℂ) * Complex.I).im)
          (Complex.ofReal_im c)
      _ = 0 + s := by
        exact congrArg (fun r : ℝ => 0 + r) hmul_im
      _ = s :=
        zero_add s
  calc
    (1 - ((c : ℂ) + (s : ℂ) * Complex.I)).im =
        (1 : ℂ).im - ((c : ℂ) + (s : ℂ) * Complex.I).im :=
      Complex.sub_im (1 : ℂ) ((c : ℂ) + (s : ℂ) * Complex.I)
    _ = 0 - ((c : ℂ) + (s : ℂ) * Complex.I).im := by
      exact congrArg
        (fun r : ℝ => r - ((c : ℂ) + (s : ℂ) * Complex.I).im)
        Complex.one_im
    _ = 0 - s := by
      exact congrArg (fun r : ℝ => 0 - r) hadd_im
    _ = -s :=
      zero_sub s

/-- The real norm-square algebra behind the inverse chord formula. -/
theorem Real.inverseChord_normSq_formula
    (ψ : ℝ) :
    (1 - Real.cos ψ) * (1 - Real.cos ψ) +
        (-Real.sin ψ) * (-Real.sin ψ) =
      2 * (1 - Real.cos ψ) := by
  exact real_inverse_chord_normsq_algebra_for_logarithmicPhase
    (s := Real.sin ψ)
    (c := Real.cos ψ)
    (Real.sin_sq_add_cos_sq ψ)

/-- Cancelling the nonzero real chord denominator in the real coordinate. -/
theorem Real.one_sub_cos_div_two_mul_one_sub_cos
    {ψ : ℝ}
    (hone_sub_cos_ne : 1 - Real.cos ψ ≠ 0) :
    (1 - Real.cos ψ) / (2 * (1 - Real.cos ψ)) = 1 / 2 := by
  have htwo_ne : (2 : ℝ) ≠ 0 :=
    two_ne_zero
  have hden_ne : 2 * (1 - Real.cos ψ) ≠ 0 :=
    mul_ne_zero htwo_ne hone_sub_cos_ne
  exact (div_eq_div_iff hden_ne htwo_ne).mpr
    (Eq.trans
      (mul_comm (1 - Real.cos ψ) 2)
      (one_mul (2 * (1 - Real.cos ψ))).symm)

/-- Removing the double negation in the imaginary coordinate quotient. -/
theorem Real.neg_neg_sin_div
    (ψ : ℝ) :
    -(-Real.sin ψ) / (2 * (1 - Real.cos ψ)) =
      Real.sin ψ / (2 * (1 - Real.cos ψ)) := by
  exact congrArg
    (fun r : ℝ => r / (2 * (1 - Real.cos ψ)))
    (neg_neg (Real.sin ψ))

/-- Coordinate formula for the inverse chord map on the punctured reduced arc. -/
theorem Complex.reducedArc_inverseGeometricDenominator_eq_half_add_imCoordFormula
    {ψ : ℝ}
    (hψ_mem : ψ ∈ Set.Ioc (-Real.pi) Real.pi)
    (hψ_ne : ψ ≠ 0) :
    Complex.reducedArc_inverseGeometricDenominator ψ =
      ((1 / 2 : ℝ) : ℂ) +
        Complex.I *
          ((Real.sin ψ / (2 * (1 - Real.cos ψ)) : ℝ) : ℂ) := by
  have hone_sub_cos_ne : 1 - Real.cos ψ ≠ 0 := by
    exact Real.one_sub_cos_ne_zero_of_mem_reducedArc hψ_mem hψ_ne
  have hden_ne : 2 * (1 - Real.cos ψ) ≠ 0 := by
    exact Real.two_mul_one_sub_cos_ne_zero_of_mem_reducedArc hψ_mem hψ_ne
  have hexp :
      Complex.exp (Complex.I * (ψ : ℂ)) =
        (Real.cos ψ : ℂ) + (Real.sin ψ : ℂ) * Complex.I := by
    calc
      Complex.exp (Complex.I * (ψ : ℂ)) =
          Complex.exp ((ψ : ℂ) * Complex.I) := by
        exact congrArg Complex.exp (mul_comm Complex.I (ψ : ℂ))
      _ = Complex.cos (ψ : ℂ) + Complex.sin (ψ : ℂ) * Complex.I :=
        Complex.exp_mul_I (ψ : ℂ)
      _ = (Real.cos ψ : ℂ) + (Real.sin ψ : ℂ) * Complex.I := by
        exact congrArg₂ Add.add
          (Complex.ofReal_cos ψ).symm
          (congrArg (fun z : ℂ => z * Complex.I)
            (Complex.ofReal_sin ψ).symm)
  let z : ℂ := 1 - Complex.exp (Complex.I * (ψ : ℂ))
  have hz_re : z.re = 1 - Real.cos ψ := by
    unfold z
    calc
      (1 - Complex.exp (Complex.I * (ψ : ℂ))).re =
          (1 - ((Real.cos ψ : ℂ) + (Real.sin ψ : ℂ) * Complex.I)).re := by
        exact congrArg Complex.re (congrArg (fun w : ℂ => 1 - w) hexp)
      _ = 1 - Real.cos ψ := by
        exact Complex.one_sub_cos_add_sin_mul_I_re (Real.cos ψ) (Real.sin ψ)
  have hz_im : z.im = -Real.sin ψ := by
    unfold z
    calc
      (1 - Complex.exp (Complex.I * (ψ : ℂ))).im =
          (1 - ((Real.cos ψ : ℂ) + (Real.sin ψ : ℂ) * Complex.I)).im := by
        exact congrArg Complex.im (congrArg (fun w : ℂ => 1 - w) hexp)
      _ = -Real.sin ψ := by
        exact Complex.one_sub_cos_add_sin_mul_I_im (Real.cos ψ) (Real.sin ψ)
  have hnormSq :
      Complex.normSq z = 2 * (1 - Real.cos ψ) := by
    calc
      Complex.normSq z = z.re * z.re + z.im * z.im :=
        Complex.normSq_apply z
      _ = (1 - Real.cos ψ) * (1 - Real.cos ψ) +
            (-Real.sin ψ) * (-Real.sin ψ) := by
        exact congrArg₂ Add.add
          (congrArg₂ Mul.mul hz_re hz_re)
          (congrArg₂ Mul.mul hz_im hz_im)
      _ = 2 * (1 - Real.cos ψ) := by
        exact Real.inverseChord_normSq_formula ψ
  exact Complex.ext
    (by
      calc
      (Complex.reducedArc_inverseGeometricDenominator ψ).re =
          z⁻¹.re := by
        rfl
      _ = z.re / Complex.normSq z :=
        Complex.inv_re z
      _ = (1 - Real.cos ψ) / (2 * (1 - Real.cos ψ)) := by
        exact congrArg₂ Div.div hz_re hnormSq
      _ = 1 / 2 := by
        exact Real.one_sub_cos_div_two_mul_one_sub_cos hone_sub_cos_ne
      _ = ((((1 / 2 : ℝ) : ℂ) +
            Complex.I *
              ((Real.sin ψ / (2 * (1 - Real.cos ψ)) : ℝ) : ℂ)).re) := by
        exact (Complex.half_add_I_mul_ofReal_re
          (Real.sin ψ / (2 * (1 - Real.cos ψ)))).symm)
    (by
      calc
      (Complex.reducedArc_inverseGeometricDenominator ψ).im =
          z⁻¹.im := by
        rfl
      _ = -z.im / Complex.normSq z :=
        Complex.inv_im z
      _ = -(-Real.sin ψ) / (2 * (1 - Real.cos ψ)) := by
        exact congrArg₂ Div.div (congrArg Neg.neg hz_im) hnormSq
      _ = Real.sin ψ / (2 * (1 - Real.cos ψ)) := by
        exact Real.neg_neg_sin_div ψ
      _ = ((((1 / 2 : ℝ) : ℂ) +
            Complex.I *
              ((Real.sin ψ / (2 * (1 - Real.cos ψ)) : ℝ) : ℂ)).im) := by
        exact (Complex.half_add_I_mul_ofReal_im
          (Real.sin ψ / (2 * (1 - Real.cos ψ)))).symm)

/-- The inverse chord map has real part `1 / 2` on the reduced arc away from
zero. -/
theorem Complex.reducedArc_inverseGeometricDenominator_re_eq_half
    {ψ : ℝ}
    (hψ_mem : ψ ∈ Set.Ioc (-Real.pi) Real.pi)
    (hψ_ne : ψ ≠ 0) :
    (Complex.reducedArc_inverseGeometricDenominator ψ).re = 1 / 2 := by
  let y : ℝ := Real.sin ψ / (2 * (1 - Real.cos ψ))
  have hformula :
      Complex.reducedArc_inverseGeometricDenominator ψ =
        ((1 / 2 : ℝ) : ℂ) + Complex.I * (y : ℂ) :=
    Complex.reducedArc_inverseGeometricDenominator_eq_half_add_imCoordFormula
      hψ_mem hψ_ne
  have hproject :
      (((1 / 2 : ℝ) : ℂ) + Complex.I * (y : ℂ)).re = 1 / 2 :=
    Complex.half_add_I_mul_ofReal_re y
  exact Eq.trans (congrArg Complex.re hformula) hproject

/-- The inverse chord map is recovered from its imaginary coordinate on the
vertical line `re = 1 / 2`. -/
theorem Complex.reducedArc_inverseGeometricDenominator_eq_lineCoord
    {ψ : ℝ}
    (hψ_mem : ψ ∈ Set.Ioc (-Real.pi) Real.pi)
    (hψ_ne : ψ ≠ 0) :
    Complex.reducedArc_inverseGeometricDenominator ψ =
      (1 / 2 : ℂ) +
        Complex.I *
          (Complex.reducedArc_inverseGeometricDenominator_imCoord ψ : ℂ) := by
  let z : ℂ := Complex.reducedArc_inverseGeometricDenominator ψ
  have hz_re : z.re = 1 / 2 :=
    Complex.reducedArc_inverseGeometricDenominator_re_eq_half hψ_mem hψ_ne
  have hz_coord :
      z = (z.re : ℂ) + Complex.I * (z.im : ℂ) := by
    calc
      z = (z.re : ℂ) + z.im * Complex.I :=
        (Complex.re_add_im z).symm
      _ = (z.re : ℂ) + Complex.I * (z.im : ℂ) := by
        exact congrArg (fun w : ℂ => (z.re : ℂ) + w)
          (mul_comm (z.im : ℂ) Complex.I)
  have hz_target :
      z = (1 / 2 : ℂ) + Complex.I * (z.im : ℂ) := by
    have hz_real_half :
        z = ((1 / 2 : ℝ) : ℂ) + Complex.I * (z.im : ℂ) :=
      Eq.subst
        (motive := fun r : ℝ =>
          z = (r : ℂ) + Complex.I * (z.im : ℂ))
        hz_re
        hz_coord
    exact Eq.trans hz_real_half
      (congrArg
        (fun q : ℂ => q + Complex.I * (z.im : ℂ))
        Complex.ofReal_one_div_two_eq_complex_one_div_two)
  exact hz_target

/-- Differences of reduced inverse denominators on the same vertical line have
norm equal to the absolute difference of their imaginary coordinates. -/
theorem Complex.reducedArc_inverseGeometricDenominator_sub_norm_eq_imCoord
    {ψ θ : ℝ}
    (hψ_mem : ψ ∈ Set.Ioc (-Real.pi) Real.pi)
    (hθ_mem : θ ∈ Set.Ioc (-Real.pi) Real.pi)
    (hψ_ne : ψ ≠ 0)
    (hθ_ne : θ ≠ 0) :
      ‖Complex.reducedArc_inverseGeometricDenominator ψ -
        Complex.reducedArc_inverseGeometricDenominator θ‖ =
      ‖Complex.reducedArc_inverseGeometricDenominator_imCoord ψ -
        Complex.reducedArc_inverseGeometricDenominator_imCoord θ‖ := by
  let zψ : ℂ := Complex.reducedArc_inverseGeometricDenominator ψ
  let zθ : ℂ := Complex.reducedArc_inverseGeometricDenominator θ
  let yψ : ℝ := Complex.reducedArc_inverseGeometricDenominator_imCoord ψ
  let yθ : ℝ := Complex.reducedArc_inverseGeometricDenominator_imCoord θ
  have hψ_line : zψ = (1 / 2 : ℂ) + Complex.I * (yψ : ℂ) :=
    Complex.reducedArc_inverseGeometricDenominator_eq_lineCoord hψ_mem hψ_ne
  have hθ_line : zθ = (1 / 2 : ℂ) + Complex.I * (yθ : ℂ) :=
    Complex.reducedArc_inverseGeometricDenominator_eq_lineCoord hθ_mem hθ_ne
  have hdiff :
      zψ - zθ = Complex.I * ((yψ - yθ : ℝ) : ℂ) := by
    calc
      zψ - zθ =
          ((1 / 2 : ℂ) + Complex.I * (yψ : ℂ)) -
            ((1 / 2 : ℂ) + Complex.I * (yθ : ℂ)) := by
        exact congrArg₂ Sub.sub hψ_line hθ_line
      _ = Complex.I * ((yψ - yθ : ℝ) : ℂ) := by
        exact Complex.half_add_I_mul_ofReal_sub_complexHalf yψ yθ
  have hnorm :
      ‖Complex.I * ((yψ - yθ : ℝ) : ℂ)‖ = ‖yψ - yθ‖ := by
    calc
      ‖Complex.I * ((yψ - yθ : ℝ) : ℂ)‖ =
          ‖Complex.I‖ * ‖((yψ - yθ : ℝ) : ℂ)‖ :=
        norm_mul Complex.I ((yψ - yθ : ℝ) : ℂ)
      _ = 1 * ‖((yψ - yθ : ℝ) : ℂ)‖ := by
        exact congrArg (fun r : ℝ => r * ‖((yψ - yθ : ℝ) : ℂ)‖) Complex.norm_I
      _ = ‖((yψ - yθ : ℝ) : ℂ)‖ :=
        one_mul ‖((yψ - yθ : ℝ) : ℂ)‖
      _ = ‖yψ - yθ‖ :=
        RCLike.norm_ofReal (yψ - yθ)
  exact Eq.trans (congrArg norm hdiff) hnorm

/-- Explicit imaginary coordinate of the inverse chord map on the reduced arc
away from zero. -/
theorem Complex.reducedArc_inverseGeometricDenominator_imCoord_eq
    {ψ : ℝ}
    (hψ_mem : ψ ∈ Set.Ioc (-Real.pi) Real.pi)
    (hψ_ne : ψ ≠ 0) :
    Complex.reducedArc_inverseGeometricDenominator_imCoord ψ =
      Real.sin ψ / (2 * (1 - Real.cos ψ)) := by
  let y : ℝ := Real.sin ψ / (2 * (1 - Real.cos ψ))
  have hformula :
      Complex.reducedArc_inverseGeometricDenominator ψ =
        ((1 / 2 : ℝ) : ℂ) + Complex.I * (y : ℂ) :=
    Complex.reducedArc_inverseGeometricDenominator_eq_half_add_imCoordFormula
      hψ_mem hψ_ne
  have hproject :
      (((1 / 2 : ℝ) : ℂ) + Complex.I * (y : ℂ)).im = y :=
    Complex.half_add_I_mul_ofReal_im y
  exact Eq.trans (congrArg Complex.im hformula) hproject


end

end LFunctions
end Boundary
