import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaTransformCalculus.ZetaTransformCalculusBase.Owner
import Mathlib.Analysis.Fourier.Inversion
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.SetIntegral

/-!
# Fixed-line Cauchy projection for logarithmic Laplace transforms

This file owns the Fourier-Cauchy multiplier theorem used by the one-pole
vertical channel.  The parent transform-calculus owner supplies only the
zeta-specific naming wrapper.
-/

namespace Boundary

open scoped Filter FourierTransform Topology
open Filter Real Complex Set MeasureTheory

noncomputable section

section FixedLineCauchyProjection

/-- The right one-pole Cauchy/Laplace projection value attached to a compactly
supported logarithmic test function. -/
noncomputable def zetaLaplaceTransform_rightOnePoleCauchyProjectionValue
    (φ : LFunctions.ZetaTestFunction) (_c : ℝ) : ℂ :=
  ∫ x in Set.Iic (0 : ℝ),
    (-2 * (Real.pi : ℂ)) *
      φ x *
        Complex.exp ((1 / 2 : ℂ) * (x : ℂ))

/-- The time-side kernel whose Fourier transform is the fixed right vertical
Laplace slice after the `s = 1` Cauchy multiplier is separated. -/
noncomputable def zetaLaplaceTransform_rightOnePoleProjectionKernel
    (φ : LFunctions.ZetaTestFunction) : ℝ → ℂ :=
  fun x : ℝ =>
    φ x *
      Complex.exp ((1 / 2 : ℂ) * (x : ℂ))

/-- Continuity of the right one-pole projection kernel. -/
theorem zetaLaplaceTransform_rightOnePoleProjectionKernel_continuous
    (φ : LFunctions.ZetaTestFunction) :
    Continuous (zetaLaplaceTransform_rightOnePoleProjectionKernel φ) :=
  φ.continuous.mul
    (Complex.continuous_exp.comp
      (continuous_const.mul Complex.continuous_ofReal))

/-- Compact support of the right one-pole projection kernel. -/
theorem zetaLaplaceTransform_rightOnePoleProjectionKernel_hasCompactSupport
    (φ : LFunctions.ZetaTestFunction) :
    HasCompactSupport (zetaLaplaceTransform_rightOnePoleProjectionKernel φ) :=
  φ.hasCompactSupport.mul_right

/-- Smoothness of the right one-pole projection kernel attached to an admissible
function. -/
theorem zetaLaplaceTransform_rightOnePoleProjectionKernel_contDiff_admissible
    (f : LFunctions.ZetaAdmissibleFunction) :
    ContDiff ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞)
      (zetaLaplaceTransform_rightOnePoleProjectionKernel f.toZetaTestFunction') := by
  have hexp :
      ContDiff ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞)
        (fun x : ℝ => Complex.exp ((1 / 2 : ℂ) * (x : ℂ))) := by
    have harg :
        ContDiff ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞)
          (fun x : ℝ => (1 / 2 : ℂ) * (x : ℂ)) := by
      exact contDiff_const.mul Complex.ofRealCLM.contDiff
    exact Complex.contDiff_exp.comp
      harg
  exact f.smooth.mul hexp

/-- Real scalar affine identity for the right-pole vertical coefficient. -/
theorem zetaLaplaceTransform_rightOnePoleProjectionKernel_verticalSlice_realAffine_eq
    (c : ℝ) :
    c - 1 / 2 = 1 / 2 + (c - 1) := by
  calc
    c - 1 / 2 = c + -(1 / 2) := by
      exact sub_eq_add_neg c (1 / 2)
    _ = c + (1 / 2 - 1) := by
      exact congrArg
        (fun r : ℝ => c + r)
        (half_sub (1 : ℝ)).symm
    _ = c + (1 / 2 + -1) := by
      exact congrArg
        (fun r : ℝ => c + r)
        (sub_eq_add_neg (1 / 2 : ℝ) 1)
    _ = (c + 1 / 2) + -1 := by
      exact (add_assoc c (1 / 2 : ℝ) (-1)).symm
    _ = (1 / 2 + c) + -1 := by
      exact congrArg
        (fun r : ℝ => r + -1)
        (add_comm c (1 / 2 : ℝ))
    _ = 1 / 2 + (c + -1) := by
      exact add_assoc (1 / 2 : ℝ) c (-1)
    _ = 1 / 2 + (c - 1) := by
      exact congrArg
        (fun r : ℝ => 1 / 2 + r)
        (sub_eq_add_neg c 1).symm

/-- Real affine coefficient identity in the right-pole vertical slice. -/
theorem zetaLaplaceTransform_rightOnePoleProjectionKernel_verticalSlice_realCoefficient_eq
    (c : ℝ) :
    (c : ℂ) - 1 / 2 = (1 / 2 : ℂ) + ((c - 1 : ℝ) : ℂ) := by
  have hhalf_coe : (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) := by
    exact (Complex.ofReal_div (1 : ℝ) (2 : ℝ)).symm
  calc
    (c : ℂ) - 1 / 2
        = (c : ℂ) - ((1 / 2 : ℝ) : ℂ) := by
          exact congrArg
            (fun z : ℂ => (c : ℂ) - z)
            hhalf_coe
    _ = ((c - 1 / 2 : ℝ) : ℂ) := by
          exact (Complex.ofReal_sub c (1 / 2)).symm
    _ = ((1 / 2 + (c - 1) : ℝ) : ℂ) := by
          exact congrArg
            (fun r : ℝ => (r : ℂ))
            (zetaLaplaceTransform_rightOnePoleProjectionKernel_verticalSlice_realAffine_eq
              c)
    _ = ((1 / 2 : ℝ) : ℂ) + ((c - 1 : ℝ) : ℂ) := by
          exact Complex.ofReal_add (1 / 2) (c - 1)
    _ = (1 / 2 : ℂ) + ((c - 1 : ℝ) : ℂ) := by
          exact congrArg
            (fun z : ℂ => z + ((c - 1 : ℝ) : ℂ))
            hhalf_coe.symm

/-- Imaginary coefficient commutation in the right-pole vertical slice. -/
theorem zetaLaplaceTransform_rightOnePoleProjectionKernel_verticalSlice_imaginaryCoefficient_eq
    (t : ℝ) :
    (t : ℂ) * Complex.I = Complex.I * (t : ℂ) :=
  mul_comm (t : ℂ) Complex.I

/-- Coefficient identity before multiplying the vertical-slice exponent by the
time variable. -/
theorem zetaLaplaceTransform_rightOnePoleProjectionKernel_verticalSlice_coefficient_eq
    (c t : ℝ) :
    ((c : ℂ) + t * Complex.I) - 1 / 2 =
      (1 / 2 : ℂ) + Complex.I * (t : ℂ) + ((c - 1 : ℝ) : ℂ) := by
  calc
    ((c : ℂ) + t * Complex.I) - 1 / 2
        = ((c : ℂ) - 1 / 2) + (t : ℂ) * Complex.I := by
          exact (add_sub_right_comm (c : ℂ) ((t : ℂ) * Complex.I) (1 / 2 : ℂ))
    _ =
        ((1 / 2 : ℂ) + ((c - 1 : ℝ) : ℂ)) + (t : ℂ) * Complex.I := by
          exact congrArg
            (fun z : ℂ => z + (t : ℂ) * Complex.I)
            (zetaLaplaceTransform_rightOnePoleProjectionKernel_verticalSlice_realCoefficient_eq
              c)
    _ =
        ((1 / 2 : ℂ) + ((c - 1 : ℝ) : ℂ)) + Complex.I * (t : ℂ) := by
          exact congrArg
            (fun z : ℂ => ((1 / 2 : ℂ) + ((c - 1 : ℝ) : ℂ)) + z)
            (zetaLaplaceTransform_rightOnePoleProjectionKernel_verticalSlice_imaginaryCoefficient_eq
              t)
    _ =
        (1 / 2 : ℂ) + (((c - 1 : ℝ) : ℂ) + Complex.I * (t : ℂ)) := by
          exact add_assoc (1 / 2 : ℂ) (((c - 1 : ℝ) : ℂ)) (Complex.I * (t : ℂ))
    _ =
        (1 / 2 : ℂ) + (Complex.I * (t : ℂ) + ((c - 1 : ℝ) : ℂ)) := by
          exact congrArg
            (fun z : ℂ => (1 / 2 : ℂ) + z)
            (add_comm (((c - 1 : ℝ) : ℂ)) (Complex.I * (t : ℂ)))
    _ =
        (1 / 2 : ℂ) + Complex.I * (t : ℂ) + ((c - 1 : ℝ) : ℂ) := by
          exact (add_assoc (1 / 2 : ℂ) (Complex.I * (t : ℂ))
            (((c - 1 : ℝ) : ℂ))).symm

/-- Exponent-coordinate identity behind the right-pole vertical slice. -/
theorem zetaLaplaceTransform_rightOnePoleProjectionKernel_verticalSlice_exponent_eq
    (c t x : ℝ) :
    ((((c : ℂ) + t * Complex.I) - 1 / 2) * (x : ℂ)) =
      (1 / 2 : ℂ) * (x : ℂ) +
        Complex.I * (t : ℂ) * (x : ℂ) +
          ((c - 1 : ℝ) : ℂ) * (x : ℂ) := by
  calc
    ((((c : ℂ) + t * Complex.I) - 1 / 2) * (x : ℂ))
        =
        (((1 / 2 : ℂ) + Complex.I * (t : ℂ) + ((c - 1 : ℝ) : ℂ)) *
          (x : ℂ)) := by
          exact congrArg
            (fun z : ℂ => z * (x : ℂ))
            (zetaLaplaceTransform_rightOnePoleProjectionKernel_verticalSlice_coefficient_eq
              c t)
    _ =
        ((1 / 2 : ℂ) + Complex.I * (t : ℂ)) * (x : ℂ) +
          ((c - 1 : ℝ) : ℂ) * (x : ℂ) :=
          add_mul
            ((1 / 2 : ℂ) + Complex.I * (t : ℂ))
            (((c - 1 : ℝ) : ℂ))
            (x : ℂ)
    _ =
        ((1 / 2 : ℂ) * (x : ℂ) +
            (Complex.I * (t : ℂ)) * (x : ℂ)) +
          ((c - 1 : ℝ) : ℂ) * (x : ℂ) := by
          exact congrArg
            (fun z : ℂ => z + ((c - 1 : ℝ) : ℂ) * (x : ℂ))
            (add_mul (1 / 2 : ℂ) (Complex.I * (t : ℂ)) (x : ℂ))
    _ =
        (1 / 2 : ℂ) * (x : ℂ) +
          Complex.I * (t : ℂ) * (x : ℂ) +
            ((c - 1 : ℝ) : ℂ) * (x : ℂ) := by
          exact rfl

/-- Pointwise exponential algebra for the right-pole vertical slice. -/
theorem zetaLaplaceTransform_rightOnePoleProjectionKernel_verticalSlice_integrand_eq
    (φ : LFunctions.ZetaTestFunction) (c t x : ℝ) :
    φ x *
        Complex.exp
          ((((c : ℂ) + t * Complex.I) - 1 / 2) * (x : ℂ)) =
      zetaLaplaceTransform_rightOnePoleProjectionKernel φ x *
          Complex.exp
            (Complex.I * (t : ℂ) * (x : ℂ)) *
        Complex.exp (((c - 1 : ℝ) : ℂ) * (x : ℂ)) := by
  unfold zetaLaplaceTransform_rightOnePoleProjectionKernel
  calc
    φ x *
        Complex.exp
          ((((c : ℂ) + t * Complex.I) - 1 / 2) * (x : ℂ))
        =
        φ x *
          Complex.exp
            ((1 / 2 : ℂ) * (x : ℂ) +
              Complex.I * (t : ℂ) * (x : ℂ) +
                ((c - 1 : ℝ) : ℂ) * (x : ℂ)) := by
          exact congrArg
            (fun z : ℂ => φ x * Complex.exp z)
            (zetaLaplaceTransform_rightOnePoleProjectionKernel_verticalSlice_exponent_eq
              c t x)
    _ =
        φ x *
          (Complex.exp
            ((1 / 2 : ℂ) * (x : ℂ) +
              Complex.I * (t : ℂ) * (x : ℂ)) *
            Complex.exp (((c - 1 : ℝ) : ℂ) * (x : ℂ))) := by
          exact congrArg
            (fun z : ℂ => φ x * z)
            (Complex.exp_add
              ((1 / 2 : ℂ) * (x : ℂ) +
                Complex.I * (t : ℂ) * (x : ℂ))
              (((c - 1 : ℝ) : ℂ) * (x : ℂ)))
    _ =
        φ x *
          ((Complex.exp ((1 / 2 : ℂ) * (x : ℂ)) *
              Complex.exp (Complex.I * (t : ℂ) * (x : ℂ))) *
            Complex.exp (((c - 1 : ℝ) : ℂ) * (x : ℂ))) := by
          exact congrArg
            (fun z : ℂ =>
              φ x * (z *
                Complex.exp (((c - 1 : ℝ) : ℂ) * (x : ℂ))))
            (Complex.exp_add
              ((1 / 2 : ℂ) * (x : ℂ))
              (Complex.I * (t : ℂ) * (x : ℂ)))
    _ =
        (φ x * Complex.exp ((1 / 2 : ℂ) * (x : ℂ))) *
            Complex.exp (Complex.I * (t : ℂ) * (x : ℂ)) *
          Complex.exp (((c - 1 : ℝ) : ℂ) * (x : ℂ)) := by
          exact
            calc
              φ x *
                  ((Complex.exp ((1 / 2 : ℂ) * (x : ℂ)) *
                      Complex.exp (Complex.I * (t : ℂ) * (x : ℂ))) *
                    Complex.exp (((c - 1 : ℝ) : ℂ) * (x : ℂ)))
                  =
                  (φ x *
                    (Complex.exp ((1 / 2 : ℂ) * (x : ℂ)) *
                      Complex.exp (Complex.I * (t : ℂ) * (x : ℂ)))) *
                    Complex.exp (((c - 1 : ℝ) : ℂ) * (x : ℂ)) := by
                    exact (mul_assoc (φ x)
                      (Complex.exp ((1 / 2 : ℂ) * (x : ℂ)) *
                        Complex.exp (Complex.I * (t : ℂ) * (x : ℂ)))
                      (Complex.exp (((c - 1 : ℝ) : ℂ) * (x : ℂ)))).symm
              _ =
                  ((φ x * Complex.exp ((1 / 2 : ℂ) * (x : ℂ))) *
                      Complex.exp (Complex.I * (t : ℂ) * (x : ℂ))) *
                    Complex.exp (((c - 1 : ℝ) : ℂ) * (x : ℂ)) := by
                    exact congrArg
                      (fun z : ℂ =>
                        z *
                          Complex.exp (((c - 1 : ℝ) : ℂ) * (x : ℂ)))
                      ((mul_assoc (φ x)
                        (Complex.exp ((1 / 2 : ℂ) * (x : ℂ)))
                        (Complex.exp (Complex.I * (t : ℂ) * (x : ℂ)))).symm)

/-- The right vertical Laplace slice, after the right-pole shift, is the
Fourier transform of the time-side projection kernel at angular frequency
`t / (2 * π)`.

This is the normalization bridge that keeps the pole projection theorem from
owning both Fourier sign conventions and Cauchy inversion at once. -/
theorem zetaLaplaceTransform_rightOnePoleProjectionKernel_verticalSlice_eq_fourier
    (φ : LFunctions.ZetaTestFunction) (c t : ℝ) :
    zetaLaplaceTransform φ (((c : ℂ) + t * Complex.I) - 1 / 2) =
      ∫ x : ℝ,
        zetaLaplaceTransform_rightOnePoleProjectionKernel φ x *
          Complex.exp
            (Complex.I * (t : ℂ) * (x : ℂ)) *
          Complex.exp (((c - 1 : ℝ) : ℂ) * (x : ℂ)) := by
  unfold zetaLaplaceTransform
  exact
    integral_congr_ae
      (Eventually.of_forall
        (fun x : ℝ =>
          zetaLaplaceTransform_rightOnePoleProjectionKernel_verticalSlice_integrand_eq
            φ c t x))

/-- Standard full-line Fourier transform of the decaying exponential kernel on
the negative half-line. -/
theorem fixedPositiveRate_fourierTransform_negativeHalfLineExponential
    (a : ℝ) (ha : 0 < a) (x : ℝ) :
    (∫ t : ℝ,
        (-1 / ((a : ℂ) + t * Complex.I)) *
          (Complex.exp (Complex.I * (t : ℂ) * (x : ℂ)) *
            Complex.exp ((a : ℂ) * (x : ℂ)))) =
      Set.indicator (Set.Iio (0 : ℝ))
        (fun _ : ℝ => (-2 * (Real.pi : ℂ))) x := by
  sorry

/-- The right-line Cauchy denominator is the positive-rate Fourier denominator
with rate `c - 1`. -/
theorem fixedRightLine_cauchyDenominator_eq_positiveRate
    (c t : ℝ) :
    (((c : ℂ) + t * Complex.I) - 1) =
      ((c - 1 : ℝ) : ℂ) + t * Complex.I := by
  calc
    (((c : ℂ) + t * Complex.I) - 1)
        = ((c : ℂ) - 1) + t * Complex.I := by
          exact add_sub_right_comm (c : ℂ) (t * Complex.I) (1 : ℂ)
    _ = ((c - 1 : ℝ) : ℂ) + t * Complex.I := by
          exact congrArg
            (fun z : ℂ => z + t * Complex.I)
            (Complex.ofReal_sub c 1).symm

/-- Scalar Cauchy kernel value on the strictly negative time half-line. -/
theorem fixedRightLine_cauchyExponentialKernel_integral_eq_negTwoPi_of_neg
    (c : ℝ) (hc : 1 < c) (x : ℝ) (hx : x < 0) :
    (∫ t : ℝ,
        (-1 / (((c : ℂ) + t * Complex.I) - 1)) *
          (Complex.exp (Complex.I * (t : ℂ) * (x : ℂ)) *
            Complex.exp (((c - 1 : ℝ) : ℂ) * (x : ℂ)))) =
      -2 * (Real.pi : ℂ) := by
  have hrate_pos : 0 < c - 1 := sub_pos.mpr hc
  calc
    (∫ t : ℝ,
        (-1 / (((c : ℂ) + t * Complex.I) - 1)) *
          (Complex.exp (Complex.I * (t : ℂ) * (x : ℂ)) *
            Complex.exp (((c - 1 : ℝ) : ℂ) * (x : ℂ))))
        =
        ∫ t : ℝ,
          (-1 / (((c - 1 : ℝ) : ℂ) + t * Complex.I)) *
            (Complex.exp (Complex.I * (t : ℂ) * (x : ℂ)) *
              Complex.exp (((c - 1 : ℝ) : ℂ) * (x : ℂ))) := by
          exact integral_congr_ae
            (Eventually.of_forall
              (fun t : ℝ =>
                congrArg
                  (fun z : ℂ =>
                    (-1 / z) *
                      (Complex.exp (Complex.I * (t : ℂ) * (x : ℂ)) *
                        Complex.exp (((c - 1 : ℝ) : ℂ) * (x : ℂ))))
                  (fixedRightLine_cauchyDenominator_eq_positiveRate c t)))
    _ =
        Set.indicator (Set.Iio (0 : ℝ))
          (fun _ : ℝ => (-2 * (Real.pi : ℂ))) x := by
          exact fixedPositiveRate_fourierTransform_negativeHalfLineExponential
            (c - 1) hrate_pos x
    _ = -2 * (Real.pi : ℂ) := by
          exact indicator_of_mem hx
            (fun _ : ℝ => (-2 * (Real.pi : ℂ)))

/-- Scalar Cauchy kernel value on the positive time half-line. -/
theorem fixedRightLine_cauchyExponentialKernel_integral_eq_zero_of_pos
    (c : ℝ) (hc : 1 < c) (x : ℝ) (hx : 0 < x) :
    (∫ t : ℝ,
        (-1 / (((c : ℂ) + t * Complex.I) - 1)) *
          (Complex.exp (Complex.I * (t : ℂ) * (x : ℂ)) *
            Complex.exp (((c - 1 : ℝ) : ℂ) * (x : ℂ)))) =
      0 := by
  have hrate_pos : 0 < c - 1 := sub_pos.mpr hc
  calc
    (∫ t : ℝ,
        (-1 / (((c : ℂ) + t * Complex.I) - 1)) *
          (Complex.exp (Complex.I * (t : ℂ) * (x : ℂ)) *
            Complex.exp (((c - 1 : ℝ) : ℂ) * (x : ℂ))))
        =
        ∫ t : ℝ,
          (-1 / (((c - 1 : ℝ) : ℂ) + t * Complex.I)) *
            (Complex.exp (Complex.I * (t : ℂ) * (x : ℂ)) *
              Complex.exp (((c - 1 : ℝ) : ℂ) * (x : ℂ))) := by
          exact integral_congr_ae
            (Eventually.of_forall
              (fun t : ℝ =>
                congrArg
                  (fun z : ℂ =>
                    (-1 / z) *
                      (Complex.exp (Complex.I * (t : ℂ) * (x : ℂ)) *
                        Complex.exp (((c - 1 : ℝ) : ℂ) * (x : ℂ))))
                  (fixedRightLine_cauchyDenominator_eq_positiveRate c t)))
    _ =
        Set.indicator (Set.Iio (0 : ℝ))
          (fun _ : ℝ => (-2 * (Real.pi : ℂ))) x := by
          exact fixedPositiveRate_fourierTransform_negativeHalfLineExponential
            (c - 1) hrate_pos x
    _ = 0 := by
          exact indicator_of_not_mem (not_mem_Iio.mpr (le_of_lt hx))
            (fun _ : ℝ => (-2 * (Real.pi : ℂ)))

/-- Scalar Cauchy kernel value on the fixed right line, away from the boundary
point `x = 0`.

The pointwise boundary value at `x = 0` is the usual half-value, but the
full-line projection only needs this identity almost everywhere in the outer
time variable. -/
theorem fixedRightLine_cauchyExponentialKernel_integral_ae_eq_oneSidedWeight
    (c : ℝ) (hc : 1 < c) (x : ℝ) :
    (x ≠ 0) →
      (∫ t : ℝ,
        (-1 / (((c : ℂ) + t * Complex.I) - 1)) *
          (Complex.exp (Complex.I * (t : ℂ) * (x : ℂ)) *
            Complex.exp (((c - 1 : ℝ) : ℂ) * (x : ℂ)))) =
        Set.indicator (Set.Iic (0 : ℝ))
          (fun _ : ℝ => (-2 * (Real.pi : ℂ))) x := by
  intro hx_ne
  if hx_neg : x < 0 then
    calc
      (∫ t : ℝ,
          (-1 / (((c : ℂ) + t * Complex.I) - 1)) *
            (Complex.exp (Complex.I * (t : ℂ) * (x : ℂ)) *
              Complex.exp (((c - 1 : ℝ) : ℂ) * (x : ℂ))))
          = -2 * (Real.pi : ℂ) := by
            exact fixedRightLine_cauchyExponentialKernel_integral_eq_negTwoPi_of_neg
              c hc x hx_neg
      _ =
          Set.indicator (Set.Iic (0 : ℝ))
            (fun _ : ℝ => (-2 * (Real.pi : ℂ))) x := by
            exact (indicator_of_mem (le_of_lt hx_neg)
              (fun _ : ℝ => (-2 * (Real.pi : ℂ)))).symm
  else
    have hx_nonneg : 0 ≤ x := le_of_not_gt hx_neg
    have hx_pos : 0 < x := lt_of_le_of_ne hx_nonneg
      (fun hzero : 0 = x => hx_ne hzero.symm)
    have hx_not_mem : x ∉ Set.Iic (0 : ℝ) := not_mem_Iic.mpr hx_pos
    calc
      (∫ t : ℝ,
          (-1 / (((c : ℂ) + t * Complex.I) - 1)) *
            (Complex.exp (Complex.I * (t : ℂ) * (x : ℂ)) *
              Complex.exp (((c - 1 : ℝ) : ℂ) * (x : ℂ))))
          = 0 := by
            exact fixedRightLine_cauchyExponentialKernel_integral_eq_zero_of_pos
              c hc x hx_pos
      _ =
          Set.indicator (Set.Iic (0 : ℝ))
            (fun _ : ℝ => (-2 * (Real.pi : ℂ))) x := by
            exact (indicator_of_not_mem hx_not_mem
              (fun _ : ℝ => (-2 * (Real.pi : ℂ)))).symm

/-- The scalar Cauchy kernel agrees almost everywhere with the one-sided
projection weight. -/
theorem fixedRightLine_cauchyExponentialKernel_integral_eventuallyEq_oneSidedWeight
    (c : ℝ) (hc : 1 < c) :
    (fun x : ℝ =>
      (∫ t : ℝ,
        (-1 / (((c : ℂ) + t * Complex.I) - 1)) *
          (Complex.exp (Complex.I * (t : ℂ) * (x : ℂ)) *
            Complex.exp (((c - 1 : ℝ) : ℂ) * (x : ℂ))))) =ᵐ[volume]
      (fun x : ℝ =>
        Set.indicator (Set.Iic (0 : ℝ))
          (fun _ : ℝ => (-2 * (Real.pi : ℂ))) x) := by
  have hzero : volume ({0} : Set ℝ) = 0 :=
    measure_singleton (0 : ℝ)
  have hcompl : ({0} : Set ℝ)ᶜ ∈ ae volume :=
    compl_mem_ae_iff.mpr hzero
  exact Filter.mem_of_superset hcompl
    (fun x hx =>
      fixedRightLine_cauchyExponentialKernel_integral_ae_eq_oneSidedWeight
        c hc x
        (fun hxeq : x = 0 => hx hxeq))

/-- Fubini interchange for the fixed-line Fourier-Cauchy full-line integral. -/
theorem fixedRightLine_fourierCauchy_fullLine_fubini_interchange
    (K : ℝ → ℂ) (hK_cont : Continuous K) (hK_compact : HasCompactSupport K)
    (c : ℝ) (hc : 1 < c) :
    (∫ t : ℝ,
        (-1 / (((c : ℂ) + t * Complex.I) - 1)) *
          (∫ x : ℝ,
            K x *
              Complex.exp
                (Complex.I * (t : ℂ) * (x : ℂ)) *
              Complex.exp (((c - 1 : ℝ) : ℂ) * (x : ℂ)))) =
      ∫ x : ℝ,
        K x *
          (∫ t : ℝ,
            (-1 / (((c : ℂ) + t * Complex.I) - 1)) *
              (Complex.exp (Complex.I * (t : ℂ) * (x : ℂ)) *
                Complex.exp (((c - 1 : ℝ) : ℂ) * (x : ℂ)))) := by
  sorry

/-- Fubini reduction of the fixed-line Fourier-Cauchy full-line integral to the
scalar Cauchy kernel value. -/
theorem fixedRightLine_fourierCauchy_fullLine_fubini_to_scalarKernel
    (K : ℝ → ℂ) (hK_cont : Continuous K) (hK_compact : HasCompactSupport K)
    (c : ℝ) (hc : 1 < c) :
    (∫ t : ℝ,
        (-1 / (((c : ℂ) + t * Complex.I) - 1)) *
          (∫ x : ℝ,
            K x *
              Complex.exp
                (Complex.I * (t : ℂ) * (x : ℂ)) *
              Complex.exp (((c - 1 : ℝ) : ℂ) * (x : ℂ)))) =
      ∫ x : ℝ,
        K x *
          Set.indicator (Set.Iic (0 : ℝ))
            (fun _ : ℝ => (-2 * (Real.pi : ℂ))) x := by
  calc
    (∫ t : ℝ,
        (-1 / (((c : ℂ) + t * Complex.I) - 1)) *
          (∫ x : ℝ,
            K x *
              Complex.exp
                (Complex.I * (t : ℂ) * (x : ℂ)) *
              Complex.exp (((c - 1 : ℝ) : ℂ) * (x : ℂ))))
        =
        ∫ x : ℝ,
          K x *
            (∫ t : ℝ,
              (-1 / (((c : ℂ) + t * Complex.I) - 1)) *
                (Complex.exp (Complex.I * (t : ℂ) * (x : ℂ)) *
                  Complex.exp (((c - 1 : ℝ) : ℂ) * (x : ℂ)))) := by
          exact fixedRightLine_fourierCauchy_fullLine_fubini_interchange
            K hK_cont hK_compact c hc
    _ =
        ∫ x : ℝ,
          K x *
            Set.indicator (Set.Iic (0 : ℝ))
              (fun _ : ℝ => (-2 * (Real.pi : ℂ))) x := by
          exact integral_congr_ae
            ((fixedRightLine_cauchyExponentialKernel_integral_eventuallyEq_oneSidedWeight
                c hc).mono
              (fun x hx =>
                congrArg
                  (fun z : ℂ => K x * z)
                  hx))

/-- The scalar Cauchy kernel indicator integral is the one-sided projection
integral. -/
theorem fixedRightLine_fourierCauchy_scalarKernelIntegral_eq_oneSidedProjection
    (K : ℝ → ℂ) :
    (∫ x : ℝ,
        K x *
          Set.indicator (Set.Iic (0 : ℝ))
            (fun _ : ℝ => (-2 * (Real.pi : ℂ))) x) =
      ∫ x in Set.Iic (0 : ℝ),
        (-2 * (Real.pi : ℂ)) * K x := by
  calc
    (∫ x : ℝ,
        K x *
          Set.indicator (Set.Iic (0 : ℝ))
            (fun _ : ℝ => (-2 * (Real.pi : ℂ))) x)
        =
        ∫ x : ℝ,
          Set.indicator (Set.Iic (0 : ℝ))
            (fun y : ℝ => (-2 * (Real.pi : ℂ)) * K y) x := by
          exact integral_congr_ae
            (Eventually.of_forall
              (fun x : ℝ =>
                if hx : x ∈ Set.Iic (0 : ℝ) then
                  calc
                    K x *
                        Set.indicator (Set.Iic (0 : ℝ))
                          (fun _ : ℝ => (-2 * (Real.pi : ℂ))) x
                        = K x * (-2 * (Real.pi : ℂ)) := by
                          exact congrArg
                            (fun z : ℂ => K x * z)
                            (indicator_of_mem hx
                              (fun _ : ℝ => (-2 * (Real.pi : ℂ))))
                    _ = (-2 * (Real.pi : ℂ)) * K x := by
                          exact mul_comm (K x) (-2 * (Real.pi : ℂ))
                    _ =
                        Set.indicator (Set.Iic (0 : ℝ))
                          (fun y : ℝ => (-2 * (Real.pi : ℂ)) * K y) x := by
                          exact (indicator_of_mem hx
                            (fun y : ℝ => (-2 * (Real.pi : ℂ)) * K y)).symm
                else
                  calc
                    K x *
                        Set.indicator (Set.Iic (0 : ℝ))
                          (fun _ : ℝ => (-2 * (Real.pi : ℂ))) x
                        = K x * 0 := by
                          exact congrArg
                            (fun z : ℂ => K x * z)
                            (indicator_of_not_mem hx
                              (fun _ : ℝ => (-2 * (Real.pi : ℂ))))
                    _ = 0 := by
                          exact mul_zero (K x)
                    _ =
                        Set.indicator (Set.Iic (0 : ℝ))
                          (fun y : ℝ => (-2 * (Real.pi : ℂ)) * K y) x := by
                          exact (indicator_of_not_mem hx
                            (fun y : ℝ => (-2 * (Real.pi : ℂ)) * K y)).symm))
    _ =
        ∫ x in Set.Iic (0 : ℝ),
          (-2 * (Real.pi : ℂ)) * K x := by
          exact integral_indicator measurableSet_Iic

/-- Generic one-sided Fourier-Cauchy inversion for a compactly supported
time-side kernel on the fixed right line. -/
theorem fixedRightLine_fourierCauchy_fullLine_oneSidedProjection
    (K : ℝ → ℂ) (hK_cont : Continuous K) (hK_compact : HasCompactSupport K)
    (c : ℝ) (hc : 1 < c) :
    (∫ t : ℝ,
        (-1 / (((c : ℂ) + t * Complex.I) - 1)) *
          (∫ x : ℝ,
            K x *
              Complex.exp
                (Complex.I * (t : ℂ) * (x : ℂ)) *
              Complex.exp (((c - 1 : ℝ) : ℂ) * (x : ℂ)))) =
      ∫ x in Set.Iic (0 : ℝ),
        (-2 * (Real.pi : ℂ)) * K x := by
  exact
    (fixedRightLine_fourierCauchy_fullLine_fubini_to_scalarKernel
      K hK_cont hK_compact c hc).trans
      (fixedRightLine_fourierCauchy_scalarKernelIntegral_eq_oneSidedProjection
        K)

/-- Full-line Cauchy inversion after the vertical slice has already been
rewritten as the Fourier transform of the right projection kernel. -/
theorem zetaLaplaceTransform_rightOnePoleProjectionKernel_fullLineCauchyValue_fourierKernel
    (φ : LFunctions.ZetaTestFunction) (c : ℝ) (hc : 1 < c) :
    (∫ t : ℝ,
        (-1 / (((c : ℂ) + t * Complex.I) - 1)) *
          (∫ x : ℝ,
            zetaLaplaceTransform_rightOnePoleProjectionKernel φ x *
              Complex.exp
                (Complex.I * (t : ℂ) * (x : ℂ)) *
              Complex.exp (((c - 1 : ℝ) : ℂ) * (x : ℂ)))) =
      zetaLaplaceTransform_rightOnePoleCauchyProjectionValue φ c := by
  calc
    (∫ t : ℝ,
        (-1 / (((c : ℂ) + t * Complex.I) - 1)) *
          (∫ x : ℝ,
            zetaLaplaceTransform_rightOnePoleProjectionKernel φ x *
              Complex.exp
                (Complex.I * (t : ℂ) * (x : ℂ)) *
              Complex.exp (((c - 1 : ℝ) : ℂ) * (x : ℂ))))
        =
        ∫ x in Set.Iic (0 : ℝ),
          (-2 * (Real.pi : ℂ)) *
            zetaLaplaceTransform_rightOnePoleProjectionKernel φ x :=
          fixedRightLine_fourierCauchy_fullLine_oneSidedProjection
            (zetaLaplaceTransform_rightOnePoleProjectionKernel φ)
            (zetaLaplaceTransform_rightOnePoleProjectionKernel_continuous φ)
            (zetaLaplaceTransform_rightOnePoleProjectionKernel_hasCompactSupport φ)
            c hc
    _ = zetaLaplaceTransform_rightOnePoleCauchyProjectionValue φ c := by
          unfold zetaLaplaceTransform_rightOnePoleCauchyProjectionValue
          unfold zetaLaplaceTransform_rightOnePoleProjectionKernel
          exact
            setIntegral_congr_fun measurableSet_Iic
              (fun x _hx =>
                (mul_assoc
                  (-2 * (Real.pi : ℂ))
                  (φ x)
                  (Complex.exp ((1 / 2 : ℂ) * (x : ℂ)))).symm)

/-- One-sided Cauchy inversion for the right projection kernel on the fixed
line.

This is the genuine analytic core: the full-line Fourier-Cauchy multiplier
integral recovers the negative-time half-line projection value. -/
theorem zetaLaplaceTransform_rightOnePoleProjectionKernel_fullLineCauchyValue
    (φ : LFunctions.ZetaTestFunction) (c : ℝ) (hc : 1 < c) :
    (∫ t : ℝ,
        (-1 / (((c : ℂ) + t * Complex.I) - 1)) *
          zetaLaplaceTransform φ
            (((c : ℂ) + t * Complex.I) - 1 / 2)) =
      zetaLaplaceTransform_rightOnePoleCauchyProjectionValue φ c := by
  calc
    (∫ t : ℝ,
        (-1 / (((c : ℂ) + t * Complex.I) - 1)) *
          zetaLaplaceTransform φ
            (((c : ℂ) + t * Complex.I) - 1 / 2))
        =
        ∫ t : ℝ,
          (-1 / (((c : ℂ) + t * Complex.I) - 1)) *
            (∫ x : ℝ,
              zetaLaplaceTransform_rightOnePoleProjectionKernel φ x *
                Complex.exp
                  (Complex.I * (t : ℂ) * (x : ℂ)) *
                Complex.exp (((c - 1 : ℝ) : ℂ) * (x : ℂ))) := by
          exact
            integral_congr_ae
              (Eventually.of_forall
                (fun t : ℝ =>
                  congrArg
                    (fun z : ℂ =>
                      (-1 / (((c : ℂ) + t * Complex.I) - 1)) * z)
                    (zetaLaplaceTransform_rightOnePoleProjectionKernel_verticalSlice_eq_fourier
                      φ c t)))
    _ = zetaLaplaceTransform_rightOnePoleCauchyProjectionValue φ c :=
          zetaLaplaceTransform_rightOnePoleProjectionKernel_fullLineCauchyValue_fourierKernel
            φ c hc

/-- Quadratic decay of the Fourier transform of the exponentially weighted
smooth compactly supported kernel on the fixed right line. -/
theorem fixedRightLine_weightedKernel_fourierIntegral_inverseQuadraticDecay
    (K : ℝ → ℂ) (hK_cont : Continuous K) (hK_compact : HasCompactSupport K)
    (hK_smooth : ContDiff ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) K)
    (c : ℝ) (hc : 1 < c) :
    ∃ B : ℝ,
      0 < B ∧
        ∀ t : ℝ,
          ‖(∫ x : ℝ,
              K x *
                Complex.exp
                  (Complex.I * (t : ℂ) * (x : ℂ)) *
                Complex.exp (((c - 1 : ℝ) : ℂ) * (x : ℂ)))‖
            ≤ B * (1 + ‖t‖) ^ (-(2 : ℤ)) := by
  sorry

/-- Imaginary part of the shifted fixed-line Cauchy denominator. -/
theorem fixedRightLine_cauchyDenominator_im
    (c t : ℝ) :
    ((((c : ℂ) + t * Complex.I) - 1).im) = t := by
  calc
    ((((c : ℂ) + t * Complex.I) - 1).im)
        = (((c : ℂ) + t * Complex.I).im) - (1 : ℂ).im := by
          exact Complex.sub_im ((c : ℂ) + t * Complex.I) 1
    _ = ((c : ℂ).im + (t * Complex.I).im) - (1 : ℂ).im := by
          exact congrArg
            (fun x : ℝ => x - (1 : ℂ).im)
            (Complex.add_im (c : ℂ) (t * Complex.I))
    _ = ((c : ℂ).im + t) - (1 : ℂ).im := by
          exact congrArg
            (fun x : ℝ => ((c : ℂ).im + x) - (1 : ℂ).im)
            (Complex.mul_I_im (t : ℂ))
    _ = (0 + t) - (1 : ℂ).im := by
          exact congrArg
            (fun x : ℝ => (x + t) - (1 : ℂ).im)
            (Complex.ofReal_im c)
    _ = (0 + t) - 0 := by
          exact congrArg
            (fun x : ℝ => (0 + t) - x)
            Complex.one_im
    _ = 0 + t := by
          exact sub_zero (0 + t)
    _ = t := by
          exact zero_add t

/-- The fixed-line Cauchy denominator norm dominates the vertical frequency. -/
theorem fixedRightLine_abs_frequency_le_cauchyDenominator_norm
    (c t : ℝ) :
    ‖t‖ ≤ ‖(((c : ℂ) + t * Complex.I) - 1)‖ := by
  have hIm :
      ((((c : ℂ) + t * Complex.I) - 1).im) = t :=
    fixedRightLine_cauchyDenominator_im c t
  have hAbsIm :
      |((((c : ℂ) + t * Complex.I) - 1).im)| ≤
        Complex.abs (((c : ℂ) + t * Complex.I) - 1) :=
    Complex.abs_im_le_abs (((c : ℂ) + t * Complex.I) - 1)
  have hNormEqAbs :
      ‖(((c : ℂ) + t * Complex.I) - 1)‖ =
        Complex.abs (((c : ℂ) + t * Complex.I) - 1) :=
    Complex.norm_eq_abs (((c : ℂ) + t * Complex.I) - 1)
  calc
    ‖t‖
        = |t| := by
          exact Real.norm_eq_abs t
    _ = |((((c : ℂ) + t * Complex.I) - 1).im)| := by
          exact congrArg abs hIm.symm
    _ ≤ Complex.abs (((c : ℂ) + t * Complex.I) - 1) := by
          exact hAbsIm
    _ = ‖(((c : ℂ) + t * Complex.I) - 1)‖ := by
          exact hNormEqAbs.symm

/-- Real part of the shifted fixed-line Cauchy denominator. -/
theorem fixedRightLine_cauchyDenominator_re
    (c t : ℝ) :
    ((((c : ℂ) + t * Complex.I) - 1).re) = c - 1 := by
  calc
    ((((c : ℂ) + t * Complex.I) - 1).re)
        = (((c : ℂ) + t * Complex.I).re) - (1 : ℂ).re := by
          exact Complex.sub_re ((c : ℂ) + t * Complex.I) 1
    _ = ((c : ℂ).re + (t * Complex.I).re) - (1 : ℂ).re := by
          exact congrArg
            (fun x : ℝ => x - (1 : ℂ).re)
            (Complex.add_re (c : ℂ) (t * Complex.I))
    _ = ((c : ℂ).re + -((t : ℂ).im)) - (1 : ℂ).re := by
          exact congrArg
            (fun x : ℝ => ((c : ℂ).re + x) - (1 : ℂ).re)
            (Complex.mul_I_re (t : ℂ))
    _ = ((c : ℂ).re + -0) - (1 : ℂ).re := by
          exact congrArg
            (fun x : ℝ => ((c : ℂ).re + -x) - (1 : ℂ).re)
            (Complex.ofReal_im t)
    _ = ((c : ℂ).re + 0) - (1 : ℂ).re := by
          exact congrArg
            (fun x : ℝ => ((c : ℂ).re + x) - (1 : ℂ).re)
            (neg_zero : -(0 : ℝ) = 0)
    _ = (c + 0) - (1 : ℂ).re := by
          exact congrArg
            (fun x : ℝ => (x + 0) - (1 : ℂ).re)
            (Complex.ofReal_re c)
    _ = (c + 0) - 1 := by
          exact congrArg
            (fun x : ℝ => (c + 0) - x)
            Complex.one_re
    _ = c - 1 := by
          exact congrArg (fun x : ℝ => x - 1) (add_zero c)

/-- The fixed-line Cauchy denominator norm dominates the horizontal distance
from the pole. -/
theorem fixedRightLine_rate_le_cauchyDenominator_norm
    (c t : ℝ) (hc : 1 < c) :
    c - 1 ≤ ‖(((c : ℂ) + t * Complex.I) - 1)‖ := by
  have hRe :
      ((((c : ℂ) + t * Complex.I) - 1).re) = c - 1 :=
    fixedRightLine_cauchyDenominator_re c t
  have hAbsRe :
      |((((c : ℂ) + t * Complex.I) - 1).re)| ≤
        Complex.abs (((c : ℂ) + t * Complex.I) - 1) :=
    Complex.abs_re_le_abs (((c : ℂ) + t * Complex.I) - 1)
  have hNormEqAbs :
      ‖(((c : ℂ) + t * Complex.I) - 1)‖ =
        Complex.abs (((c : ℂ) + t * Complex.I) - 1) :=
    Complex.norm_eq_abs (((c : ℂ) + t * Complex.I) - 1)
  have hRateNonnegative :
      0 ≤ c - 1 :=
    (sub_pos.mpr hc).le
  calc
    c - 1
        = |c - 1| := by
          exact (abs_of_nonneg hRateNonnegative).symm
    _ = |((((c : ℂ) + t * Complex.I) - 1).re)| := by
          exact congrArg abs hRe.symm
    _ ≤ Complex.abs (((c : ℂ) + t * Complex.I) - 1) := by
          exact hAbsRe
    _ = ‖(((c : ℂ) + t * Complex.I) - 1)‖ := by
          exact hNormEqAbs.symm

/-- The fixed-line Cauchy denominator is nonzero on the right of the pole. -/
theorem fixedRightLine_cauchyDenominator_ne_zero
    (c t : ℝ) (hc : 1 < c) :
    (((c : ℂ) + t * Complex.I) - 1) ≠ 0 := by
  have hRealPart :
      ((((c : ℂ) + t * Complex.I) - 1).re) = c - 1 := by
    exact fixedRightLine_cauchyDenominator_re c t
  have hPositive :
      0 < c - 1 :=
    sub_pos.mpr hc
  exact
    fun hZero =>
      (ne_of_gt hPositive)
        (Eq.trans hRealPart (congrArg Complex.re hZero))

/-- The reciprocal of the fixed-line Cauchy denominator is bounded after
multiplication by the Japanese bracket. -/
theorem fixedRightLine_cauchyMultiplier_bracketed_bound
    (c : ℝ) (hc : 1 < c) (t : ℝ) :
    ‖(-1 / (((c : ℂ) + t * Complex.I) - 1))‖ * (1 + ‖t‖)
      ≤ 1 + (c - 1)⁻¹ := by
  have hDenomNe :
      (((c : ℂ) + t * Complex.I) - 1) ≠ 0 :=
    fixedRightLine_cauchyDenominator_ne_zero c t hc
  have hFreq :
      ‖t‖ ≤ ‖(((c : ℂ) + t * Complex.I) - 1)‖ :=
    fixedRightLine_abs_frequency_le_cauchyDenominator_norm c t
  have hRatePos :
      0 < c - 1 :=
    sub_pos.mpr hc
  have hRateNorm :
      c - 1 ≤ ‖(((c : ℂ) + t * Complex.I) - 1)‖ := by
    exact fixedRightLine_rate_le_cauchyDenominator_norm c t hc
  have hDenomPos :
      0 < ‖(((c : ℂ) + t * Complex.I) - 1)‖ :=
    norm_pos_iff.mpr hDenomNe
  calc
    ‖(-1 / (((c : ℂ) + t * Complex.I) - 1))‖ * (1 + ‖t‖)
        =
        ‖(((c : ℂ) + t * Complex.I) - 1)‖⁻¹ * (1 + ‖t‖) := by
          have hNormNegOne :
              ‖(-1 : ℂ)‖ = 1 := by
            calc
              ‖(-1 : ℂ)‖ = ‖(1 : ℂ)‖ := by
                exact norm_neg (1 : ℂ)
              _ = 1 := by
                exact norm_one
          calc
            ‖(-1 / (((c : ℂ) + t * Complex.I) - 1))‖ * (1 + ‖t‖)
                =
                (‖(-1 : ℂ)‖ / ‖(((c : ℂ) + t * Complex.I) - 1)‖) *
                  (1 + ‖t‖) := by
                  exact congrArg
                    (fun x : ℝ => x * (1 + ‖t‖))
                    (norm_div (-1 : ℂ) (((c : ℂ) + t * Complex.I) - 1))
            _ =
                (1 / ‖(((c : ℂ) + t * Complex.I) - 1)‖) *
                  (1 + ‖t‖) := by
                  exact congrArg
                    (fun x : ℝ =>
                      (x / ‖(((c : ℂ) + t * Complex.I) - 1)‖) *
                        (1 + ‖t‖))
                    hNormNegOne
            _ =
                ‖(((c : ℂ) + t * Complex.I) - 1)‖⁻¹ * (1 + ‖t‖) := by
                  exact congrArg
                    (fun x : ℝ => x * (1 + ‖t‖))
                    (one_div ‖(((c : ℂ) + t * Complex.I) - 1)‖)
    _ =
        ‖(((c : ℂ) + t * Complex.I) - 1)‖⁻¹ +
          ‖(((c : ℂ) + t * Complex.I) - 1)‖⁻¹ * ‖t‖ := by
          calc
            ‖(((c : ℂ) + t * Complex.I) - 1)‖⁻¹ * (1 + ‖t‖)
                =
                ‖(((c : ℂ) + t * Complex.I) - 1)‖⁻¹ * 1 +
                  ‖(((c : ℂ) + t * Complex.I) - 1)‖⁻¹ * ‖t‖ := by
                  exact mul_add
                    ‖(((c : ℂ) + t * Complex.I) - 1)‖⁻¹
                    1
                    ‖t‖
            _ =
                ‖(((c : ℂ) + t * Complex.I) - 1)‖⁻¹ +
                  ‖(((c : ℂ) + t * Complex.I) - 1)‖⁻¹ * ‖t‖ := by
                  exact congrArg
                    (fun x : ℝ =>
                      x +
                        ‖(((c : ℂ) + t * Complex.I) - 1)‖⁻¹ * ‖t‖)
                    (mul_one ‖(((c : ℂ) + t * Complex.I) - 1)‖⁻¹)
    _ ≤
        (c - 1)⁻¹ + 1 := by
          exact add_le_add
            (inv_le_inv_of_le hRatePos hRateNorm)
            (inv_mul_le_one₀ hFreq hDenomPos.le)
    _ = 1 + (c - 1)⁻¹ := by
          exact add_comm ((c - 1)⁻¹) 1

/-- The fixed right Cauchy multiplier contributes one inverse power on the
vertical frequency variable. -/
theorem fixedRightLine_cauchyMultiplier_norm_inverseLinearBound
    (c : ℝ) (hc : 1 < c) :
    ∃ D : ℝ,
      0 < D ∧
        ∀ t : ℝ,
          ‖(-1 / (((c : ℂ) + t * Complex.I) - 1))‖
            ≤ D * (1 + ‖t‖) ^ (-(1 : ℤ)) := by
  have hRatePos :
      0 < c - 1 :=
    sub_pos.mpr hc
  have hDpos :
      0 < 1 + (c - 1)⁻¹ :=
    add_pos zero_lt_one (inv_pos.mpr hRatePos)
  exact
    ⟨1 + (c - 1)⁻¹,
      And.intro
        hDpos
        (fun t : ℝ =>
          have hBracketPos :
              0 < 1 + ‖t‖ :=
            lt_of_lt_of_le zero_lt_one
              (le_add_of_nonneg_right (norm_nonneg t))
          have hBracketed :
              ‖(-1 / (((c : ℂ) + t * Complex.I) - 1))‖ *
                  (1 + ‖t‖)
                ≤ 1 + (c - 1)⁻¹ :=
            fixedRightLine_cauchyMultiplier_bracketed_bound c hc t
          calc
            ‖(-1 / (((c : ℂ) + t * Complex.I) - 1))‖
                ≤ (1 + (c - 1)⁻¹) / (1 + ‖t‖) := by
                  exact (le_div_iff₀ hBracketPos).mpr hBracketed
            _ =
                (1 + (c - 1)⁻¹) * (1 + ‖t‖) ^ (-(1 : ℤ)) := by
                  calc
                    (1 + (c - 1)⁻¹) / (1 + ‖t‖)
                        =
                        (1 + (c - 1)⁻¹) * (1 + ‖t‖)⁻¹ := by
                          exact div_eq_mul_inv
                            (1 + (c - 1)⁻¹)
                            (1 + ‖t‖)
                    _ =
                        (1 + (c - 1)⁻¹) *
                          (1 + ‖t‖) ^ (-(1 : ℤ)) := by
                          exact congrArg
                            (fun x : ℝ => (1 + (c - 1)⁻¹) * x)
                            (zpow_neg_one (1 + ‖t‖)).symm)⟩

/-- Japanese-bracket z-powers multiply additively in the exponents used by the
Cauchy multiplier and Fourier-kernel decay estimates. -/
theorem one_add_norm_zpow_negOne_mul_negTwo_eq_negThree
    (t : ℝ) :
    (1 + ‖t‖) ^ (-(1 : ℤ)) *
        (1 + ‖t‖) ^ (-(2 : ℤ)) =
      (1 + ‖t‖) ^ (-(3 : ℤ)) := by
  have hpos : 0 < 1 + ‖t‖ := by
    exact lt_of_lt_of_le zero_lt_one (le_add_of_nonneg_right (norm_nonneg t))
  have hne : (1 + ‖t‖) ≠ 0 := ne_of_gt hpos
  calc
    (1 + ‖t‖) ^ (-(1 : ℤ)) *
        (1 + ‖t‖) ^ (-(2 : ℤ))
        = (1 + ‖t‖) ^ ((-(1 : ℤ)) + (-(2 : ℤ))) := by
          exact (zpow_add₀ hne (-(1 : ℤ)) (-(2 : ℤ))).symm
    _ = (1 + ‖t‖) ^ (-(3 : ℤ)) := by
          exact rfl

/-- Multiplying inverse-linear and inverse-quadratic bounds gives the
inverse-cubic multiplier-integrand bound. -/
theorem fixedRightLine_cauchyMultiplier_times_fourierIntegral_inverseCubicBound
    (F : ℝ → ℂ) (M : ℝ → ℂ)
    (B D : ℝ) (hB : 0 < B) (hD : 0 < D)
    (hF :
      ∀ t : ℝ,
        ‖F t‖ ≤ B * (1 + ‖t‖) ^ (-(2 : ℤ)))
    (hM :
      ∀ t : ℝ,
        ‖M t‖ ≤ D * (1 + ‖t‖) ^ (-(1 : ℤ))) :
    ∃ C : ℝ,
      0 < C ∧
        ∀ t : ℝ,
          ‖M t * F t‖ ≤ C * (1 + ‖t‖) ^ (-(3 : ℤ)) := by
  refine ⟨D * B, mul_pos hD hB, ?_⟩
  intro t
  have hM_nonneg : 0 ≤ ‖M t‖ := norm_nonneg (M t)
  have hF_nonneg : 0 ≤ ‖F t‖ := norm_nonneg (F t)
  have hbracket_nonneg_one : 0 ≤ (1 + ‖t‖) ^ (-(1 : ℤ)) := by
    exact zpow_nonneg
      (le_trans zero_le_one (le_add_of_nonneg_right (norm_nonneg t)))
      (-(1 : ℤ))
  have hbracket_nonneg_two : 0 ≤ (1 + ‖t‖) ^ (-(2 : ℤ)) := by
    exact zpow_nonneg
      (le_trans zero_le_one (le_add_of_nonneg_right (norm_nonneg t)))
      (-(2 : ℤ))
  have hM_bound_nonneg : 0 ≤ D * (1 + ‖t‖) ^ (-(1 : ℤ)) :=
    mul_nonneg (le_of_lt hD) hbracket_nonneg_one
  have hF_bound_nonneg : 0 ≤ B * (1 + ‖t‖) ^ (-(2 : ℤ)) :=
    mul_nonneg (le_of_lt hB) hbracket_nonneg_two
  calc
    ‖M t * F t‖ = ‖M t‖ * ‖F t‖ := by
      exact norm_mul (M t) (F t)
    _ ≤
        (D * (1 + ‖t‖) ^ (-(1 : ℤ))) *
          (B * (1 + ‖t‖) ^ (-(2 : ℤ))) := by
          exact mul_le_mul (hM t) (hF t) hF_nonneg hM_bound_nonneg
    _ =
        (D * B) *
          ((1 + ‖t‖) ^ (-(1 : ℤ)) *
            (1 + ‖t‖) ^ (-(2 : ℤ))) := by
          calc
            (D * (1 + ‖t‖) ^ (-(1 : ℤ))) *
                (B * (1 + ‖t‖) ^ (-(2 : ℤ)))
                = ((D * (1 + ‖t‖) ^ (-(1 : ℤ))) * B) *
                    (1 + ‖t‖) ^ (-(2 : ℤ)) := by
                    exact (mul_assoc
                      (D * (1 + ‖t‖) ^ (-(1 : ℤ)))
                      B
                      ((1 + ‖t‖) ^ (-(2 : ℤ)))).symm
            _ = (D * ((1 + ‖t‖) ^ (-(1 : ℤ)) * B)) *
                    (1 + ‖t‖) ^ (-(2 : ℤ)) := by
                    exact congrArg
                      (fun z : ℝ => z * (1 + ‖t‖) ^ (-(2 : ℤ)))
                      (mul_assoc D
                        ((1 + ‖t‖) ^ (-(1 : ℤ)))
                        B)
            _ = (D * (B * (1 + ‖t‖) ^ (-(1 : ℤ)))) *
                    (1 + ‖t‖) ^ (-(2 : ℤ)) := by
                    exact congrArg
                      (fun z : ℝ => (D * z) * (1 + ‖t‖) ^ (-(2 : ℤ)))
                      (mul_comm ((1 + ‖t‖) ^ (-(1 : ℤ))) B)
            _ = ((D * B) * (1 + ‖t‖) ^ (-(1 : ℤ))) *
                    (1 + ‖t‖) ^ (-(2 : ℤ)) := by
                    exact congrArg
                      (fun z : ℝ => z * (1 + ‖t‖) ^ (-(2 : ℤ)))
                      ((mul_assoc D B ((1 + ‖t‖) ^ (-(1 : ℤ)))).symm)
            _ = (D * B) *
                  ((1 + ‖t‖) ^ (-(1 : ℤ)) *
                    (1 + ‖t‖) ^ (-(2 : ℤ))) := by
                    exact mul_assoc (D * B)
                      ((1 + ‖t‖) ^ (-(1 : ℤ)))
                      ((1 + ‖t‖) ^ (-(2 : ℤ)))
    _ = (D * B) * (1 + ‖t‖) ^ (-(3 : ℤ)) := by
          exact congrArg
            (fun z : ℝ => (D * B) * z)
            (one_add_norm_zpow_negOne_mul_negTwo_eq_negThree t)

/-- The fixed-line Fourier-Cauchy multiplier integrand has cubic decay for a
smooth compactly supported time kernel. -/
theorem fixedRightLine_fourierCauchy_multiplierIntegrand_inverseCubicDecay
    (K : ℝ → ℂ) (hK_cont : Continuous K) (hK_compact : HasCompactSupport K)
    (hK_smooth : ContDiff ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) K)
    (c : ℝ) (hc : 1 < c) :
    ∃ C : ℝ,
      0 < C ∧
        ∀ t : ℝ,
          ‖(-1 / (((c : ℂ) + t * Complex.I) - 1)) *
              (∫ x : ℝ,
                K x *
                  Complex.exp
                    (Complex.I * (t : ℂ) * (x : ℂ)) *
                  Complex.exp (((c - 1 : ℝ) : ℂ) * (x : ℂ)))‖
            ≤ C * (1 + ‖t‖) ^ (-(3 : ℤ)) := by
  exact
    Exists.elim
      (fixedRightLine_weightedKernel_fourierIntegral_inverseQuadraticDecay
        K hK_cont hK_compact hK_smooth c hc)
      (fun B hB =>
        Exists.elim
          (fixedRightLine_cauchyMultiplier_norm_inverseLinearBound c hc)
          (fun D hD =>
            fixedRightLine_cauchyMultiplier_times_fourierIntegral_inverseCubicBound
              (fun t : ℝ =>
                ∫ x : ℝ,
                  K x *
                    Complex.exp
                      (Complex.I * (t : ℂ) * (x : ℂ)) *
                    Complex.exp (((c - 1 : ℝ) : ℂ) * (x : ℂ)))
              (fun t : ℝ =>
                -1 / (((c : ℂ) + t * Complex.I) - 1))
              B D hB.left hD.left hB.right hD.right))

/-- A cofinal height schedule is eventually nonnegative. -/
theorem cofinalHeight_eventually_nonnegative
    (height : ℝ → ℝ) (hcofinal : Tendsto height atTop atTop) :
    ∀ᶠ u in atTop, 0 ≤ height u := by
  exact hcofinal.eventually_ge_atTop 0

/-- On a nonnegative tail, the inverse-cubic norm weight is the translated
real-power weight. -/
theorem real_inverseCubic_rightTail_value_eq_shifted_rpow
    (T t : ℝ) (hT : 0 ≤ T) (ht : t ∈ Set.Ici T) :
    (1 + ‖t‖) ^ (-(3 : ℤ)) = (t + 1) ^ (-(3 : ℝ)) := by
  have ht_nonneg : 0 ≤ t :=
    le_trans hT ht
  have hnorm : ‖t‖ = t :=
    Real.norm_of_nonneg ht_nonneg
  calc
    (1 + ‖t‖) ^ (-(3 : ℤ))
        = (1 + t) ^ (-(3 : ℤ)) := by
          exact congrArg (fun x : ℝ => x ^ (-(3 : ℤ)))
            (congrArg (fun x : ℝ => 1 + x) hnorm)
    _ = (1 + t) ^ (-(3 : ℝ)) := by
          exact (Real.rpow_intCast (1 + t) (-(3 : ℤ))).symm
    _ = (t + 1) ^ (-(3 : ℝ)) := by
          exact congrArg (fun x : ℝ => x ^ (-(3 : ℝ))) (add_comm 1 t)

/-- Lebesgue measure on the real line is preserved by right translation. -/
theorem real_volume_preserving_addRight (a : ℝ) :
    MeasurePreserving (fun x : ℝ => x + a) volume volume := by
  exact
    { measurable := measurable_add_const a
      map_eq := map_add_right_eq_self volume a }

/-- Set-integral change of variables for translating a right ray by one. -/
theorem real_setIntegral_Ici_addRight_one
    (T : ℝ) (f : ℝ → ℝ) :
    (∫ t in Set.Ici T, f (t + 1))
      =
    (∫ u in Set.Ici (T + 1), f u) := by
  have hpres :
      MeasurePreserving (fun x : ℝ => x + 1) volume volume :=
    real_volume_preserving_addRight 1
  have hemb :
      MeasurableEmbedding (fun x : ℝ => x + 1) :=
    (Homeomorph.addRight (1 : ℝ)).isClosedEmbedding.measurableEmbedding
  have himage :
      (fun x : ℝ => x + 1) '' Set.Ici T = Set.Ici (T + 1) :=
    image_add_const_Ici
  have hmap :
      (∫ u in (fun x : ℝ => x + 1) '' Set.Ici T, f u)
        =
      (∫ t in Set.Ici T, f (t + 1)) :=
    hpres.setIntegral_image_emb hemb f (Set.Ici T)
  exact
    Eq.trans hmap.symm
      (congrArg (fun s : Set ℝ => ∫ u in s, f u) himage)

/-- Removing the endpoint from the translated right ray does not change the
Lebesgue integral. -/
theorem real_setIntegral_Ici_shifted_eq_Ioi
    (T : ℝ) (f : ℝ → ℝ) :
    (∫ u in Set.Ici (T + 1), f u)
      =
    (∫ u in Set.Ioi (1 + T), f u) := by
  have hendpoint :
      (∫ u in Set.Ici (T + 1), f u)
        =
      (∫ u in Set.Ioi (T + 1), f u) :=
    integral_Ici_eq_integral_Ioi
  have hadd :
      T + 1 = 1 + T :=
    add_comm T 1
  exact
    Eq.trans hendpoint
      (congrArg (fun a : ℝ => ∫ u in Set.Ioi a, f u) hadd)

/-- On a nonnegative right tail, the inverse-cubic norm majorant is the
translated open-tail power integral. -/
theorem real_inverseCubic_rightTail_integral_eq_shifted_rpow_Ioi
    (T : ℝ) (hT : 0 ≤ T) :
    (∫ t in Set.Ici T,
        (1 + ‖t‖) ^ (-(3 : ℤ)) : ℝ)
      =
    (∫ u in Set.Ioi (1 + T),
        u ^ (-(3 : ℝ)) : ℝ) := by
  let shiftedWeight : ℝ → ℝ :=
    fun u : ℝ => u ^ (-(3 : ℝ))
  have hpoint :
      EqOn
        (fun t : ℝ => (1 + ‖t‖) ^ (-(3 : ℤ)) : ℝ)
        (fun t : ℝ => shiftedWeight (t + 1))
        (Set.Ici T) :=
    fun t ht =>
      real_inverseCubic_rightTail_value_eq_shifted_rpow T t hT ht
  have hclosed :
      (∫ t in Set.Ici T,
          (1 + ‖t‖) ^ (-(3 : ℤ)) : ℝ)
        =
      (∫ t in Set.Ici T,
          shiftedWeight (t + 1)) :=
    setIntegral_congr_fun measurableSet_Ici hpoint
  have htranslated :
      (∫ t in Set.Ici T,
          shiftedWeight (t + 1))
        =
      (∫ u in Set.Ici (T + 1),
          shiftedWeight u) :=
    real_setIntegral_Ici_addRight_one T shiftedWeight
  have hopen :
      (∫ u in Set.Ici (T + 1),
          shiftedWeight u)
        =
      (∫ u in Set.Ioi (1 + T),
          shiftedWeight u) :=
    real_setIntegral_Ici_shifted_eq_Ioi T shiftedWeight
  exact Eq.trans hclosed (Eq.trans htranslated hopen)

/-- Numeric comparison needed for the inverse-cubic improper integral. -/
theorem negThree_lt_negOne_real :
    (-(3 : ℝ)) < -1 := by
  exact neg_lt_neg one_lt_three

/-- The exponent arithmetic in the `-3` tail antiderivative. -/
theorem negThree_add_one_eq_negTwo_real :
    (-(3 : ℝ) + 1) = -(2 : ℝ) := by
  have hThree :
      (3 : ℝ) = 2 + 1 :=
    Nat.cast_add 2 1
  calc
    (-(3 : ℝ) + 1)
        = -(2 + 1 : ℝ) + 1 := by
          exact congrArg (fun x : ℝ => -x + 1) hThree
    _ = (-(2 : ℝ) + -(1 : ℝ)) + 1 := by
          exact congrArg (fun x : ℝ => x + 1) (neg_add (2 : ℝ) 1)
    _ = -(2 : ℝ) + (-(1 : ℝ) + 1) := by
          exact add_assoc (-(2 : ℝ)) (-(1 : ℝ)) 1
    _ = -(2 : ℝ) + 0 := by
          exact congrArg (fun x : ℝ => -(2 : ℝ) + x) (neg_add_cancel (1 : ℝ))
    _ = -(2 : ℝ) := by
          exact add_zero (-(2 : ℝ))

/-- Division by two written in the orientation needed by the tail value. -/
theorem div_two_eq_half_mul_real (x : ℝ) :
    x / (2 : ℝ) = (1 / 2 : ℝ) * x := by
  have hOneDiv :
      (1 / 2 : ℝ) = (2 : ℝ)⁻¹ :=
    one_div (2 : ℝ)
  calc
    x / (2 : ℝ)
        = x * (2 : ℝ)⁻¹ := by
          exact div_eq_mul_inv x (2 : ℝ)
    _ = x * (1 / 2 : ℝ) := by
          exact congrArg (fun y : ℝ => x * y) hOneDiv.symm
    _ = (1 / 2 : ℝ) * x := by
          exact mul_comm x (1 / 2 : ℝ)

/-- The signed denominator in the `-3` tail antiderivative contributes the
factor `1 / 2`. -/
theorem neg_div_negTwo_eq_half_mul_real (x : ℝ) :
    -x / (-(2 : ℝ)) = (1 / 2 : ℝ) * x := by
  calc
    -x / (-(2 : ℝ))
        = x / (2 : ℝ) := by
          exact neg_div_neg_eq x (2 : ℝ)
    _ = (1 / 2 : ℝ) * x := by
          exact div_two_eq_half_mul_real x

/-- Transporting a real power across the `-3 + 1 = -2` exponent equality. -/
theorem rpow_negThree_add_one_eq_rpow_negTwo_real (c : ℝ) :
    c ^ (-(3 : ℝ) + 1) = c ^ (-(2 : ℝ)) := by
  exact congrArg (fun a : ℝ => c ^ a) negThree_add_one_eq_negTwo_real

/-- The antiderivative boundary value appearing in
`integral_Ioi_rpow_of_lt` for exponent `-3` is the expected half
inverse-square value. -/
theorem real_negThree_rpow_tail_antiderivative_value_eq_half_rpow_negTwo
    (c : ℝ) :
    -(c ^ (-(3 : ℝ) + 1)) / (-(3 : ℝ) + 1)
      =
    (1 / 2 : ℝ) * c ^ (-(2 : ℝ)) := by
  calc
    -(c ^ (-(3 : ℝ) + 1)) / (-(3 : ℝ) + 1)
        =
        -(c ^ (-(2 : ℝ))) / (-(2 : ℝ)) := by
          exact
            congrArg₂
              (fun x y : ℝ => -x / y)
              (rpow_negThree_add_one_eq_rpow_negTwo_real c)
              negThree_add_one_eq_negTwo_real
    _ = (1 / 2 : ℝ) * c ^ (-(2 : ℝ)) := by
          exact neg_div_negTwo_eq_half_mul_real (c ^ (-(2 : ℝ)))

/-- Specialization of the standard improper-integral computation to the
translated inverse-cubic power tail. -/
theorem real_shifted_rpow_Ioi_negThree_integral_eq_half_rpow_negTwo
    (T : ℝ) (hT : 0 ≤ T) :
    (∫ u in Set.Ioi (1 + T),
        u ^ (-(3 : ℝ)) : ℝ)
      =
    (1 / 2 : ℝ) * (1 + T) ^ (-(2 : ℝ)) := by
  have hPositiveLower :
      0 < 1 + T :=
    lt_of_lt_of_le zero_lt_one (le_add_of_nonneg_right hT)
  have hIntegral :
      (∫ u in Set.Ioi (1 + T),
          u ^ (-(3 : ℝ)) : ℝ)
        =
      -((1 + T) ^ (-(3 : ℝ) + 1)) / (-(3 : ℝ) + 1) :=
    integral_Ioi_rpow_of_lt (a := -(3 : ℝ)) (c := 1 + T)
      negThree_lt_negOne_real
      hPositiveLower
  calc
    (∫ u in Set.Ioi (1 + T),
        u ^ (-(3 : ℝ)) : ℝ)
        =
        -((1 + T) ^ (-(3 : ℝ) + 1)) / (-(3 : ℝ) + 1) := by
          exact hIntegral
    _ =
        (1 / 2 : ℝ) * (1 + T) ^ (-(2 : ℝ)) := by
          exact real_negThree_rpow_tail_antiderivative_value_eq_half_rpow_negTwo
            (1 + T)

/-- On a nonnegative center, the shifted real-power boundary value is the same
as the integer-power norm boundary value used downstream. -/
theorem real_shifted_rpow_negTwo_eq_inverseQuadratic_boundary
    (T : ℝ) (hT : 0 ≤ T) :
    (1 + T) ^ (-(2 : ℝ))
      =
    (1 + ‖T‖) ^ (-(2 : ℤ)) := by
  calc
    (1 + T) ^ (-(2 : ℝ))
        =
        (1 + ‖T‖) ^ (-(2 : ℝ)) := by
          exact congrArg
            (fun x : ℝ => (1 + x) ^ (-(2 : ℝ)))
            (Real.norm_of_nonneg hT).symm
    _ =
        (1 + ‖T‖) ^ (-(2 : ℤ)) := by
          exact Real.rpow_intCast (1 + ‖T‖) (-(2 : ℤ))

/-- The translated open inverse-cubic power tail has the sharp inverse-square
boundary value. -/
theorem real_shifted_rpow_Ioi_negThree_integral_eq_half_inverseQuadratic
    (T : ℝ) (hT : 0 ≤ T) :
    (∫ u in Set.Ioi (1 + T),
        u ^ (-(3 : ℝ)) : ℝ)
      =
    (1 / 2 : ℝ) * (1 + ‖T‖) ^ (-(2 : ℤ)) := by
  calc
    (∫ u in Set.Ioi (1 + T),
        u ^ (-(3 : ℝ)) : ℝ)
        =
        (1 / 2 : ℝ) * (1 + T) ^ (-(2 : ℝ)) := by
          exact real_shifted_rpow_Ioi_negThree_integral_eq_half_rpow_negTwo
            T hT
    _ =
        (1 / 2 : ℝ) * (1 + ‖T‖) ^ (-(2 : ℤ)) := by
          exact congrArg
            (fun x : ℝ => (1 / 2 : ℝ) * x)
            (real_shifted_rpow_negTwo_eq_inverseQuadratic_boundary T hT)

/-- The inverse-cubic norm majorant is invariant under real reflection. -/
theorem real_inverseCubic_reflection_value (t : ℝ) :
    (1 + ‖(-t)‖) ^ (-(3 : ℤ))
      =
    ((1 + ‖t‖) ^ (-(3 : ℤ)) : ℝ) := by
  exact congrArg (fun x : ℝ => (1 + x) ^ (-(3 : ℤ))) (norm_neg t)

/-- Reflecting the right closed tail across the origin gives the left closed
tail. -/
theorem preimage_neg_Ici_eq_Iic_neg (T : ℝ) :
    (fun t : ℝ => -t) ⁻¹' Set.Ici T = Set.Iic (-T) := by
  exact Set.ext (fun _ => le_neg)

/-- The reflected inverse-cubic set integral over the left tail is the
unreflected set integral over that same left tail. -/
theorem real_inverseCubic_leftTail_integral_eq_reflected_preimage
    (T : ℝ) :
    (∫ t in Set.Iic (-T),
        (1 + ‖t‖) ^ (-(3 : ℤ)) : ℝ)
      =
    (∫ t in (fun x : ℝ => -x) ⁻¹' Set.Ici T,
        (1 + ‖(-t)‖) ^ (-(3 : ℤ)) : ℝ) := by
  have hSet :
      (fun t : ℝ => -t) ⁻¹' Set.Ici T = Set.Iic (-T) :=
    preimage_neg_Ici_eq_Iic_neg T
  have hPoint :
      ∀ t : ℝ,
        t ∈ Set.Iic (-T) →
          (1 + ‖t‖) ^ (-(3 : ℤ))
            =
          ((1 + ‖(-t)‖) ^ (-(3 : ℤ)) : ℝ) :=
    fun t _ =>
      (real_inverseCubic_reflection_value t).symm
  calc
    (∫ t in Set.Iic (-T),
        (1 + ‖t‖) ^ (-(3 : ℤ)) : ℝ)
        =
        (∫ t in Set.Iic (-T),
          (1 + ‖(-t)‖) ^ (-(3 : ℤ)) : ℝ) := by
          exact setIntegral_congr_fun measurableSet_Iic hPoint
    _ =
        (∫ t in (fun x : ℝ => -x) ⁻¹' Set.Ici T,
          (1 + ‖(-t)‖) ^ (-(3 : ℤ)) : ℝ) := by
          exact congrArg
            (fun s : Set ℝ =>
              ∫ t in s, (1 + ‖(-t)‖) ^ (-(3 : ℤ)) : ℝ)
            hSet.symm

/-- Set-integral change of variables for real reflection on the inverse-cubic
tail. -/
theorem real_inverseCubic_reflected_preimage_integral_eq_rightTail
    (T : ℝ) :
    (∫ t in (fun x : ℝ => -x) ⁻¹' Set.Ici T,
        (1 + ‖(-t)‖) ^ (-(3 : ℤ)) : ℝ)
      =
    (∫ t in Set.Ici T,
        (1 + ‖t‖) ^ (-(3 : ℤ)) : ℝ) := by
  exact
    (Measure.measurePreserving_neg (volume : Measure ℝ)).setIntegral_preimage_emb
      (Homeomorph.neg ℝ).measurableEmbedding
      (fun t : ℝ => (1 + ‖t‖) ^ (-(3 : ℤ)) : ℝ)
      (Set.Ici T)

/-- The left closed inverse-cubic norm tail is the corresponding right closed
tail by the reflection symmetry of Lebesgue measure and the norm. -/
theorem real_inverseCubic_leftTail_integral_eq_rightTail
    (T : ℝ) :
    (∫ t in Set.Iic (-T),
        (1 + ‖t‖) ^ (-(3 : ℤ)) : ℝ)
      =
    (∫ t in Set.Ici T,
        (1 + ‖t‖) ^ (-(3 : ℤ)) : ℝ) := by
  calc
    (∫ t in Set.Iic (-T),
        (1 + ‖t‖) ^ (-(3 : ℤ)) : ℝ)
        =
        (∫ t in (fun x : ℝ => -x) ⁻¹' Set.Ici T,
          (1 + ‖(-t)‖) ^ (-(3 : ℤ)) : ℝ) := by
          exact real_inverseCubic_leftTail_integral_eq_reflected_preimage T
    _ =
        (∫ t in Set.Ici T,
          (1 + ‖t‖) ^ (-(3 : ℤ)) : ℝ) := by
          exact real_inverseCubic_reflected_preimage_integral_eq_rightTail T

/-- Sharp right half-line inverse-cubic tail evaluation up to the harmless
closed-endpoint convention. -/
theorem real_inverseCubic_rightTail_integral_half_inverseQuadratic
    (T : ℝ) (hT : 0 ≤ T) :
    (∫ t in Set.Ici T,
        (1 + ‖t‖) ^ (-(3 : ℤ)) : ℝ)
      ≤ (1 / 2 : ℝ) * (1 + ‖T‖) ^ (-(2 : ℤ)) := by
  calc
    (∫ t in Set.Ici T,
        (1 + ‖t‖) ^ (-(3 : ℤ)) : ℝ)
        =
        (∫ u in Set.Ioi (1 + T),
          u ^ (-(3 : ℝ)) : ℝ) := by
          exact real_inverseCubic_rightTail_integral_eq_shifted_rpow_Ioi T hT
    _ =
        (1 / 2 : ℝ) * (1 + ‖T‖) ^ (-(2 : ℤ)) := by
          exact real_shifted_rpow_Ioi_negThree_integral_eq_half_inverseQuadratic
            T hT
    _ ≤
        (1 / 2 : ℝ) * (1 + ‖T‖) ^ (-(2 : ℤ)) := by
          exact le_rfl

/-- Sharp left half-line inverse-cubic tail evaluation up to the harmless
closed-endpoint convention. -/
theorem real_inverseCubic_leftTail_integral_half_inverseQuadratic
    (T : ℝ) (hT : 0 ≤ T) :
    (∫ t in Set.Iic (-T),
        (1 + ‖t‖) ^ (-(3 : ℤ)) : ℝ)
      ≤ (1 / 2 : ℝ) * (1 + ‖T‖) ^ (-(2 : ℤ)) := by
  calc
    (∫ t in Set.Iic (-T),
        (1 + ‖t‖) ^ (-(3 : ℤ)) : ℝ)
        =
        (∫ t in Set.Ici T,
          (1 + ‖t‖) ^ (-(3 : ℤ)) : ℝ) := by
          exact real_inverseCubic_leftTail_integral_eq_rightTail T
    _ ≤
        (1 / 2 : ℝ) * (1 + ‖T‖) ^ (-(2 : ℤ)) := by
          exact real_inverseCubic_rightTail_integral_half_inverseQuadratic T hT

/-- The coefficient `1 / 2` is bounded by `2`. -/
theorem one_half_le_two_real :
    (1 / 2 : ℝ) ≤ 2 := by
  have hhalf_le_one :
      (1 / 2 : ℝ) ≤ 1 :=
    one_div_le_one zero_le_one one_le_two
  exact le_trans hhalf_le_one one_le_two

/-- The inverse-quadratic boundary term is nonnegative. -/
theorem real_inverseQuadratic_boundary_nonnegative
    (T : ℝ) :
    0 ≤ ((1 + ‖T‖) ^ (-(2 : ℤ)) : ℝ) := by
  exact zpow_nonneg (add_nonneg zero_le_one (norm_nonneg T)) (-(2 : ℤ))

/-- The sharp half-coefficient inverse-quadratic bound implies the looser
coefficient used downstream. -/
theorem real_inverseCubic_halfBound_le_twoBound
    (T : ℝ) :
    (1 / 2 : ℝ) * (1 + ‖T‖) ^ (-(2 : ℤ))
      ≤ 2 * (1 + ‖T‖) ^ (-(2 : ℤ)) := by
  exact mul_le_mul_of_nonneg_right
    one_half_le_two_real
    (real_inverseQuadratic_boundary_nonnegative T)

/-- Right half-line inverse-cubic tail bound. -/
theorem real_inverseCubic_rightTail_integral_inverseQuadratic
    (T : ℝ) (hT : 0 ≤ T) :
    (∫ t in Set.Ici T,
        (1 + ‖t‖) ^ (-(3 : ℤ)) : ℝ)
      ≤ 2 * (1 + ‖T‖) ^ (-(2 : ℤ)) := by
  exact le_trans
    (real_inverseCubic_rightTail_integral_half_inverseQuadratic T hT)
    (real_inverseCubic_halfBound_le_twoBound T)

/-- Left half-line inverse-cubic tail bound. -/
theorem real_inverseCubic_leftTail_integral_inverseQuadratic
    (T : ℝ) (hT : 0 ≤ T) :
    (∫ t in Set.Iic (-T),
        (1 + ‖t‖) ^ (-(3 : ℤ)) : ℝ)
      ≤ 2 * (1 + ‖T‖) ^ (-(2 : ℤ)) := by
  exact le_trans
    (real_inverseCubic_leftTail_integral_half_inverseQuadratic T hT)
    (real_inverseCubic_halfBound_le_twoBound T)

/-- The complement of a symmetric interval is contained in the union of the two
outer half-lines. -/
theorem compl_symmetricIcc_subset_leftTail_union_rightTail
    (T : ℝ) :
    (Set.Icc (-T) T)ᶜ ⊆ Set.Iic (-T) ∪ Set.Ici T := by
  intro x hx
  by_cases hleft : x ≤ -T
  · exact Or.inl hleft
  · have hneg_left : -T < x := lt_of_not_ge hleft
    have hT_le_x : T ≤ x := by
      by_contra hxT
      exact hx ⟨le_of_lt hneg_left, le_of_not_ge hxT⟩
    exact Or.inr hT_le_x

/-- Pointwise nonnegativity of the scalar inverse-cubic majorant. -/
theorem real_inverseCubic_pointwise_nonnegative
    (t : ℝ) :
    0 ≤ ((1 + ‖t‖) ^ (-(3 : ℤ)) : ℝ) := by
  exact zpow_nonneg (add_nonneg zero_le_one (norm_nonneg t)) (-(3 : ℤ))

/-- The scalar inverse-cubic majorant is nonnegative almost everywhere on any
tail union. -/
theorem real_inverseCubic_tailUnion_ae_nonnegative
    (T : ℝ) :
    0 ≤ᵐ[volume.restrict (Set.Iic (-T) ∪ Set.Ici T)]
      (fun t : ℝ => (1 + ‖t‖) ^ (-(3 : ℤ)) : ℝ) := by
  exact Eventually.of_forall
    (fun t : ℝ => real_inverseCubic_pointwise_nonnegative t)

/-- The scalar inverse-cubic majorant is globally integrable. -/
theorem real_inverseCubic_integrable :
    Integrable
      (fun t : ℝ => (1 + ‖t‖) ^ (-(3 : ℤ)) : ℝ) := by
  have hDimension :
      ((Module.finrank ℝ ℝ : ℕ) : ℝ) = 1 := by
    exact congrArg
      (fun n : ℕ => (n : ℝ))
      (Module.finrank_self ℝ)
  have hDimensionBound :
      ((Module.finrank ℝ ℝ : ℕ) : ℝ) < 3 := by
    calc
      ((Module.finrank ℝ ℝ : ℕ) : ℝ) = 1 := by
        exact hDimension
      _ < 3 := by
        exact one_lt_three
  have hRpow :
      Integrable
        (fun t : ℝ => (1 + ‖t‖) ^ (-(3 : ℝ)) : ℝ) :=
    integrable_one_add_norm (E := ℝ) (μ := volume) hDimensionBound
  exact hRpow.congr
    (Eventually.of_forall
      (fun t : ℝ =>
        Real.rpow_intCast (1 + ‖t‖) (-(3 : ℤ))))

/-- Integrability of the scalar inverse-cubic majorant on a closed right
half-line tail. -/
theorem real_inverseCubic_integrableOn_rightTail
    (T : ℝ) :
    IntegrableOn
      (fun t : ℝ => (1 + ‖t‖) ^ (-(3 : ℤ)) : ℝ)
      (Set.Ici T) := by
  exact real_inverseCubic_integrable.integrableOn

/-- Integrability of the scalar inverse-cubic majorant on a closed left
half-line tail. -/
theorem real_inverseCubic_integrableOn_leftTail
    (T : ℝ) :
    IntegrableOn
      (fun t : ℝ => (1 + ‖t‖) ^ (-(3 : ℤ)) : ℝ)
      (Set.Iic (-T)) := by
  exact real_inverseCubic_integrable.integrableOn

/-- Integrability of the scalar inverse-cubic majorant on the union of the two
outer closed half-line tails. -/
theorem real_inverseCubic_integrableOn_leftTail_union_rightTail
    (T : ℝ) :
    IntegrableOn
      (fun t : ℝ => (1 + ‖t‖) ^ (-(3 : ℤ)) : ℝ)
      (Set.Iic (-T) ∪ Set.Ici T) := by
  exact
    (real_inverseCubic_integrableOn_leftTail T).union
      (real_inverseCubic_integrableOn_rightTail T)

/-- For a nonnegative radius, the intersection of the two closed outer tails is
subsingleton. -/
theorem leftTail_rightTail_inter_subsingleton_of_nonnegative
    (T : ℝ) (hT : 0 ≤ T) :
    (Set.Iic (-T) ∩ Set.Ici T).Subsingleton := by
  have hNegT_le_T : -T ≤ T :=
    le_trans (neg_nonpos.mpr hT) hT
  exact (Set.subsingleton_Icc_of_ge hNegT_le_T).mono
    (fun x hx => ⟨hx.right, hx.left⟩)

/-- The two closed tails are a.e.-disjoint with respect to Lebesgue measure
when the center radius is nonnegative. -/
theorem leftTail_rightTail_aedisjoint_of_nonnegative
    (T : ℝ) (hT : 0 ≤ T) :
    AEDisjoint volume (Set.Iic (-T)) (Set.Ici T) := by
  exact
    (leftTail_rightTail_inter_subsingleton_of_nonnegative T hT).measure_zero
      volume

/-- The scalar inverse-cubic integral over the two-tail union is bounded by the
sum of the two closed-tail integrals. -/
theorem real_inverseCubic_tailUnionIntegral_le_left_plus_right
    (T : ℝ) (hT : 0 ≤ T) :
    (∫ t in Set.Iic (-T) ∪ Set.Ici T,
        (1 + ‖t‖) ^ (-(3 : ℤ)) : ℝ)
      ≤
        (∫ t in Set.Iic (-T),
          (1 + ‖t‖) ^ (-(3 : ℤ)) : ℝ) +
        (∫ t in Set.Ici T,
          (1 + ‖t‖) ^ (-(3 : ℤ)) : ℝ) := by
  have hIntegrableUnion :
      IntegrableOn
        (fun t : ℝ => (1 + ‖t‖) ^ (-(3 : ℤ)) : ℝ)
        (Set.Iic (-T) ∪ Set.Ici T) :=
    real_inverseCubic_integrableOn_leftTail_union_rightTail T
  have hIntegrableLeft :
      IntegrableOn
        (fun t : ℝ => (1 + ‖t‖) ^ (-(3 : ℤ)) : ℝ)
        (Set.Iic (-T)) :=
    hIntegrableUnion.left_of_union
  have hIntegrableRight :
      IntegrableOn
        (fun t : ℝ => (1 + ‖t‖) ^ (-(3 : ℤ)) : ℝ)
        (Set.Ici T) :=
    hIntegrableUnion.right_of_union
  calc
    (∫ t in Set.Iic (-T) ∪ Set.Ici T,
        (1 + ‖t‖) ^ (-(3 : ℤ)) : ℝ)
        =
        (∫ t in Set.Iic (-T),
          (1 + ‖t‖) ^ (-(3 : ℤ)) : ℝ) +
        (∫ t in Set.Ici T,
          (1 + ‖t‖) ^ (-(3 : ℤ)) : ℝ) := by
          exact integral_union_ae
            (leftTail_rightTail_aedisjoint_of_nonnegative T hT)
            measurableSet_Ici.nullMeasurableSet
            hIntegrableLeft
            hIntegrableRight
    _ ≤
        (∫ t in Set.Iic (-T),
          (1 + ‖t‖) ^ (-(3 : ℤ)) : ℝ) +
        (∫ t in Set.Ici T,
          (1 + ‖t‖) ^ (-(3 : ℤ)) : ℝ) := by
          exact le_rfl

/-- The symmetric complement inverse-cubic integral is bounded by the sum of
the two half-line tail integrals. -/
theorem real_inverseCubic_symmetricComplementIntegral_le_left_plus_right
    (T : ℝ) (hT : 0 ≤ T) :
    (∫ t in (Set.Icc (-T) T)ᶜ,
        (1 + ‖t‖) ^ (-(3 : ℤ)) : ℝ)
      ≤
        (∫ t in Set.Iic (-T),
          (1 + ‖t‖) ^ (-(3 : ℤ)) : ℝ) +
        (∫ t in Set.Ici T,
          (1 + ‖t‖) ^ (-(3 : ℤ)) : ℝ) := by
  have hUnionIntegrable :
      IntegrableOn
        (fun t : ℝ => (1 + ‖t‖) ^ (-(3 : ℤ)) : ℝ)
        (Set.Iic (-T) ∪ Set.Ici T) :=
    real_inverseCubic_integrableOn_leftTail_union_rightTail T
  have hNonnegative :
      0 ≤ᵐ[volume.restrict (Set.Iic (-T) ∪ Set.Ici T)]
        (fun t : ℝ => (1 + ‖t‖) ^ (-(3 : ℤ)) : ℝ) :=
    real_inverseCubic_tailUnion_ae_nonnegative T
  have hSubset :
      (Set.Icc (-T) T)ᶜ ≤ᵐ[volume] Set.Iic (-T) ∪ Set.Ici T :=
    (compl_symmetricIcc_subset_leftTail_union_rightTail T).eventuallyLE
  calc
    (∫ t in (Set.Icc (-T) T)ᶜ,
        (1 + ‖t‖) ^ (-(3 : ℤ)) : ℝ)
        ≤
        (∫ t in Set.Iic (-T) ∪ Set.Ici T,
          (1 + ‖t‖) ^ (-(3 : ℤ)) : ℝ) := by
          exact setIntegral_mono_set hUnionIntegrable hNonnegative hSubset
    _ ≤
        (∫ t in Set.Iic (-T),
          (1 + ‖t‖) ^ (-(3 : ℤ)) : ℝ) +
        (∫ t in Set.Ici T,
          (1 + ‖t‖) ^ (-(3 : ℤ)) : ℝ) := by
          exact real_inverseCubic_tailUnionIntegral_le_left_plus_right T hT

/-- Fixed-height inverse-cubic tails outside a symmetric interval have
inverse-quadratic size. -/
theorem real_inverseCubic_symmetricComplementIntegral_inverseQuadratic_of_nonnegative
    (T : ℝ) (hT : 0 ≤ T) :
    (∫ t in (Set.Icc (-T) T)ᶜ,
        (1 + ‖t‖) ^ (-(3 : ℤ)) : ℝ)
      ≤ 4 * (1 + ‖T‖) ^ (-(2 : ℤ)) := by
  have hleft :
      (∫ t in Set.Iic (-T),
          (1 + ‖t‖) ^ (-(3 : ℤ)) : ℝ)
        ≤ 2 * (1 + ‖T‖) ^ (-(2 : ℤ)) :=
    real_inverseCubic_leftTail_integral_inverseQuadratic T hT
  have hright :
      (∫ t in Set.Ici T,
          (1 + ‖t‖) ^ (-(3 : ℤ)) : ℝ)
        ≤ 2 * (1 + ‖T‖) ^ (-(2 : ℤ)) :=
    real_inverseCubic_rightTail_integral_inverseQuadratic T hT
  calc
    (∫ t in (Set.Icc (-T) T)ᶜ,
        (1 + ‖t‖) ^ (-(3 : ℤ)) : ℝ)
        ≤
          (∫ t in Set.Iic (-T),
            (1 + ‖t‖) ^ (-(3 : ℤ)) : ℝ) +
          (∫ t in Set.Ici T,
            (1 + ‖t‖) ^ (-(3 : ℤ)) : ℝ) := by
          exact real_inverseCubic_symmetricComplementIntegral_le_left_plus_right T hT
    _ ≤
        2 * (1 + ‖T‖) ^ (-(2 : ℤ)) +
          2 * (1 + ‖T‖) ^ (-(2 : ℤ)) := by
          exact add_le_add hleft hright
    _ = 4 * (1 + ‖T‖) ^ (-(2 : ℤ)) := by
          calc
            2 * (1 + ‖T‖) ^ (-(2 : ℤ)) +
                2 * (1 + ‖T‖) ^ (-(2 : ℤ))
                =
                (2 + 2) * (1 + ‖T‖) ^ (-(2 : ℤ)) := by
                  exact (add_mul 2 2 ((1 + ‖T‖) ^ (-(2 : ℤ)))).symm
            _ = 4 * (1 + ‖T‖) ^ (-(2 : ℤ)) := by
                  exact rfl

/-- The real inverse-cubic majorant has inverse-quadratic tails outside
symmetric intervals. -/
theorem real_inverseCubic_symmetricComplementIntegral_inverseQuadratic
    (height : ℝ → ℝ) (hcofinal : Tendsto height atTop atTop) :
    ∃ A : ℝ,
      0 < A ∧
        ∀ᶠ u in atTop,
          (∫ t in (Set.Icc (-(height u)) (height u))ᶜ,
              (1 + ‖t‖) ^ (-(3 : ℤ)) : ℝ)
            ≤ A * (1 + ‖height u‖) ^ (-(2 : ℤ)) := by
  refine ⟨4, by exact zero_lt_four, ?_⟩
  exact (cofinalHeight_eventually_nonnegative height hcofinal).mono
    (fun u hu =>
      real_inverseCubic_symmetricComplementIntegral_inverseQuadratic_of_nonnegative
        (height u) hu)

/-- Norm domination by an inverse-cubic majorant controls the symmetric
Bochner tail by the corresponding scalar majorant tail. -/
theorem fixedRightLine_integrableFunction_symmetricTail_norm_le_majorantTail
    (G : ℝ → ℂ) (hG_aesm : AEStronglyMeasurable G volume)
    (C : ℝ) (hC : 0 < C)
    (height : ℝ → ℝ)
    (hG :
      ∀ t : ℝ,
        ‖G t‖ ≤ C * (1 + ‖t‖) ^ (-(3 : ℤ))) :
    ∀ᶠ u in atTop,
      ‖(∫ t in Set.Icc (-(height u)) (height u), G t) -
          (∫ t : ℝ, G t)‖
        ≤ C *
          (∫ t in (Set.Icc (-(height u)) (height u))ᶜ,
            (1 + ‖t‖) ^ (-(3 : ℤ)) : ℝ) := by
  have hMajorantIntegrable :
      Integrable
        (fun t : ℝ => C * ((1 + ‖t‖) ^ (-(3 : ℤ)) : ℝ))
        volume :=
    real_inverseCubic_integrable.const_mul C
  have hG_integrable : Integrable G volume :=
    hMajorantIntegrable.mono' hG_aesm
      (Eventually.of_forall hG)
  exact Filter.Eventually.of_forall
    (fun u : ℝ =>
      let s : Set ℝ := Set.Icc (-(height u)) (height u)
      have hs : MeasurableSet s :=
        measurableSet_Icc
      have hcompl :
          ∫ t in sᶜ, G t = ∫ t : ℝ, G t - ∫ t in s, G t :=
        setIntegral_compl hs hG_integrable
      have hdiff :
          (∫ t in s, G t) - (∫ t : ℝ, G t)
            =
          -(∫ t in sᶜ, G t) := by
        calc
          (∫ t in s, G t) - (∫ t : ℝ, G t)
              =
            -((∫ t : ℝ, G t) - (∫ t in s, G t)) := by
              exact (neg_sub (∫ t : ℝ, G t) (∫ t in s, G t)).symm
          _ = -(∫ t in sᶜ, G t) := by
              exact congrArg Neg.neg hcompl.symm
      have hnormComplement :
          ‖(∫ t in s, G t) - (∫ t : ℝ, G t)‖
            =
          ‖∫ t in sᶜ, G t‖ := by
        calc
          ‖(∫ t in s, G t) - (∫ t : ℝ, G t)‖
              = ‖-(∫ t in sᶜ, G t)‖ := by
                exact congrArg norm hdiff
          _ = ‖∫ t in sᶜ, G t‖ := by
                exact norm_neg (∫ t in sᶜ, G t)
      have hNormIntegral :
          ‖∫ t in sᶜ, G t‖
            ≤
          ∫ t in sᶜ, ‖G t‖ :=
        norm_integral_le_integral_norm
          (μ := volume.restrict sᶜ) G
      have hMajorantOn :
          ∫ t in sᶜ, ‖G t‖
            ≤
          ∫ t in sᶜ,
            C * ((1 + ‖t‖) ^ (-(3 : ℤ)) : ℝ) :=
        setIntegral_mono_on
          hG_integrable.norm.integrableOn
          hMajorantIntegrable.integrableOn
          hs.compl
          (fun t _ht => hG t)
      have hConstOut :
          (∫ t in sᶜ,
            C * ((1 + ‖t‖) ^ (-(3 : ℤ)) : ℝ))
            =
          C *
            (∫ t in sᶜ,
              ((1 + ‖t‖) ^ (-(3 : ℤ)) : ℝ)) :=
        integral_mul_left (μ := volume.restrict sᶜ) C
          (fun t : ℝ => ((1 + ‖t‖) ^ (-(3 : ℤ)) : ℝ))
      calc
        ‖(∫ t in Set.Icc (-(height u)) (height u), G t) -
            (∫ t : ℝ, G t)‖
            = ‖(∫ t in s, G t) - (∫ t : ℝ, G t)‖ := by
              exact rfl
        _ = ‖∫ t in sᶜ, G t‖ := by
              exact hnormComplement
        _ ≤ ∫ t in sᶜ, ‖G t‖ := by
              exact hNormIntegral
        _ ≤
            ∫ t in sᶜ,
              C * ((1 + ‖t‖) ^ (-(3 : ℤ)) : ℝ) := by
              exact hMajorantOn
        _ = C *
            (∫ t in sᶜ,
              ((1 + ‖t‖) ^ (-(3 : ℤ)) : ℝ)) := by
              exact hConstOut)

/-- Inverse-cubic pointwise decay gives an inverse-quadratic symmetric
truncation tail along any cofinal height schedule. -/
theorem fixedRightLine_integrableFunction_symmetricTail_inverseQuadratic_of_inverseCubicDecay
    (G : ℝ → ℂ) (hG_aesm : AEStronglyMeasurable G volume)
    (height : ℝ → ℝ) (hcofinal : Tendsto height atTop atTop)
    (C : ℝ) (hC : 0 < C)
    (hG :
      ∀ t : ℝ,
        ‖G t‖ ≤ C * (1 + ‖t‖) ^ (-(3 : ℤ))) :
    ∃ MR : ℝ,
      0 < MR ∧
        ∀ᶠ u in atTop,
          ‖(∫ t in Set.Icc (-(height u)) (height u), G t) -
              (∫ t : ℝ, G t)‖
            ≤ MR * (1 + ‖height u‖) ^ (-(2 : ℤ)) := by
  match real_inverseCubic_symmetricComplementIntegral_inverseQuadratic height hcofinal with
  | ⟨A, hA_pos, hA_eventual⟩ =>
      refine ⟨C * A, mul_pos hC hA_pos, ?_⟩
      exact
        ((fixedRightLine_integrableFunction_symmetricTail_norm_le_majorantTail
          G hG_aesm C hC height hG).and hA_eventual).mono
          (fun u hu =>
            calc
              ‖(∫ t in Set.Icc (-(height u)) (height u), G t) -
                  (∫ t : ℝ, G t)‖
                  ≤ C *
                    (∫ t in (Set.Icc (-(height u)) (height u))ᶜ,
                      (1 + ‖t‖) ^ (-(3 : ℤ)) : ℝ) := hu.1
              _ ≤ C * (A * (1 + ‖height u‖) ^ (-(2 : ℤ))) := by
                    exact mul_le_mul_of_nonneg_left hu.2 (le_of_lt hC)
              _ = C * A * (1 + ‖height u‖) ^ (-(2 : ℤ)) := by
                    exact (mul_assoc C A
                      ((1 + ‖height u‖) ^ (-(2 : ℤ)))).symm)

/-- The fixed right-line Fourier-Cauchy multiplier integrand is strongly
measurable in the frequency variable. -/
theorem fixedRightLine_fourierCauchy_multiplierIntegrand_aestronglyMeasurable
    (K : ℝ → ℂ) (hK_cont : Continuous K) (hK_compact : HasCompactSupport K)
    (hK_smooth : ContDiff ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) K)
    (c : ℝ) (hc : 1 < c) :
    AEStronglyMeasurable
      (fun t : ℝ =>
        (-1 / (((c : ℂ) + t * Complex.I) - 1)) *
          (∫ x : ℝ,
            K x *
              Complex.exp
                (Complex.I * (t : ℂ) * (x : ℂ)) *
              Complex.exp (((c - 1 : ℝ) : ℂ) * (x : ℂ))))
      volume := by
  have hK_pair :
      Continuous (fun p : ℝ × ℝ => K p.2) :=
    hK_cont.comp continuous_snd
  have hphase :
      Continuous
        (fun p : ℝ × ℝ =>
          Complex.I * (p.1 : ℂ) * (p.2 : ℂ)) :=
    (continuous_const.mul
      (Complex.continuous_ofReal.comp continuous_fst)).mul
        (Complex.continuous_ofReal.comp continuous_snd)
  have hweight :
      Continuous
        (fun p : ℝ × ℝ =>
          (((c - 1 : ℝ) : ℂ) * (p.2 : ℂ))) :=
    continuous_const.mul
      (Complex.continuous_ofReal.comp continuous_snd)
  have hjoint :
      Continuous
        (fun p : ℝ × ℝ =>
          K p.2 *
            Complex.exp
              (Complex.I * (p.1 : ℂ) * (p.2 : ℂ)) *
            Complex.exp (((c - 1 : ℝ) : ℂ) * (p.2 : ℂ))) :=
    (hK_pair.mul (Complex.continuous_exp.comp hphase)).mul
      (Complex.continuous_exp.comp hweight)
  have hinner :
      AEStronglyMeasurable
        (fun t : ℝ =>
          ∫ x : ℝ,
            K x *
              Complex.exp
                (Complex.I * (t : ℂ) * (x : ℂ)) *
              Complex.exp (((c - 1 : ℝ) : ℂ) * (x : ℂ)))
        volume :=
    (hjoint.stronglyMeasurable.integral_prod_right').aestronglyMeasurable
  have hden :
      Measurable
        (fun t : ℝ => (((c : ℂ) + t * Complex.I) - 1)) :=
    ((measurable_const.add
      ((Complex.continuous_ofReal.measurable).mul measurable_const)).sub
      measurable_const)
  have hmultiplier :
      AEStronglyMeasurable
        (fun t : ℝ => -1 / (((c : ℂ) + t * Complex.I) - 1))
        volume :=
    ((measurable_const.div hden).aestronglyMeasurable)
  exact hmultiplier.mul hinner

/-- Generic inverse-quadratic truncation tail for the fixed right
Fourier-Cauchy multiplier. -/
theorem fixedRightLine_fourierCauchy_truncationTail_inverseQuadratic
    (K : ℝ → ℂ) (hK_cont : Continuous K) (hK_compact : HasCompactSupport K)
    (hK_smooth : ContDiff ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) K)
    (c : ℝ) (hc : 1 < c)
    (height : ℝ → ℝ) (hcofinal : Tendsto height atTop atTop) :
    ∃ MR : ℝ,
      0 < MR ∧
        ∀ᶠ u in atTop,
          ‖(∫ t in Set.Icc (-(height u)) (height u),
              (-1 / (((c : ℂ) + t * Complex.I) - 1)) *
                (∫ x : ℝ,
                  K x *
                    Complex.exp
                      (Complex.I * (t : ℂ) * (x : ℂ)) *
                    Complex.exp (((c - 1 : ℝ) : ℂ) * (x : ℂ)))) -
            (∫ t : ℝ,
              (-1 / (((c : ℂ) + t * Complex.I) - 1)) *
                (∫ x : ℝ,
                  K x *
                    Complex.exp
                      (Complex.I * (t : ℂ) * (x : ℂ)) *
                    Complex.exp (((c - 1 : ℝ) : ℂ) * (x : ℂ))))‖
            ≤ MR * (1 + ‖height u‖) ^ (-(2 : ℤ)) := by
  match
    fixedRightLine_fourierCauchy_multiplierIntegrand_inverseCubicDecay
      K hK_cont hK_compact hK_smooth c hc
  with
  | ⟨C, hC_pos, hC_bound⟩ =>
      exact
        fixedRightLine_integrableFunction_symmetricTail_inverseQuadratic_of_inverseCubicDecay
          (fun t : ℝ =>
            (-1 / (((c : ℂ) + t * Complex.I) - 1)) *
              (∫ x : ℝ,
                K x *
                  Complex.exp
                    (Complex.I * (t : ℂ) * (x : ℂ)) *
                  Complex.exp (((c - 1 : ℝ) : ℂ) * (x : ℂ))))
          (fixedRightLine_fourierCauchy_multiplierIntegrand_aestronglyMeasurable
            K hK_cont hK_compact hK_smooth c hc)
          height hcofinal C hC_pos hC_bound

/-- Inverse-quadratic truncation control for the fixed right Cauchy multiplier
after its full-line Cauchy value has been identified. -/
theorem zetaLaplaceTransform_rightOnePoleProjectionKernel_truncationTail_inverseQuadratic
    (f : LFunctions.ZetaAdmissibleFunction) (c : ℝ) (hc : 1 < c)
    (height : ℝ → ℝ) (hcofinal : Tendsto height atTop atTop) :
    ∃ MR : ℝ,
      0 < MR ∧
        ∀ᶠ u in atTop,
          ‖(∫ t in Set.Icc (-(height u)) (height u),
              (-1 / (((c : ℂ) + t * Complex.I) - 1)) *
                zetaLaplaceTransform f.toZetaTestFunction'
                  (((c : ℂ) + t * Complex.I) - 1 / 2)) -
            (∫ t : ℝ,
              (-1 / (((c : ℂ) + t * Complex.I) - 1)) *
                zetaLaplaceTransform f.toZetaTestFunction'
                  (((c : ℂ) + t * Complex.I) - 1 / 2))‖
            ≤ MR * (1 + ‖height u‖) ^ (-(2 : ℤ)) := by
  match
    fixedRightLine_fourierCauchy_truncationTail_inverseQuadratic
      (zetaLaplaceTransform_rightOnePoleProjectionKernel f.toZetaTestFunction')
      (zetaLaplaceTransform_rightOnePoleProjectionKernel_continuous f.toZetaTestFunction')
      (zetaLaplaceTransform_rightOnePoleProjectionKernel_hasCompactSupport f.toZetaTestFunction')
      (zetaLaplaceTransform_rightOnePoleProjectionKernel_contDiff_admissible f)
      c hc height hcofinal
  with
  | ⟨MR, hMR_pos, hMR_eventual⟩ =>
      exact ⟨MR, hMR_pos,
        hMR_eventual.mono
          (fun u hu =>
            let hfinite :
                (∫ t in Set.Icc (-(height u)) (height u),
                    (-1 / (((c : ℂ) + t * Complex.I) - 1)) *
                      zetaLaplaceTransform f.toZetaTestFunction'
                        (((c : ℂ) + t * Complex.I) - 1 / 2)) =
                  (∫ t in Set.Icc (-(height u)) (height u),
                    (-1 / (((c : ℂ) + t * Complex.I) - 1)) *
                      (∫ x : ℝ,
                        zetaLaplaceTransform_rightOnePoleProjectionKernel f.toZetaTestFunction' x *
                          Complex.exp
                            (Complex.I * (t : ℂ) * (x : ℂ)) *
                          Complex.exp (((c - 1 : ℝ) : ℂ) * (x : ℂ)))) :=
                setIntegral_congr_fun measurableSet_Icc
                  (fun t _ht =>
                    congrArg
                      (fun z : ℂ =>
                        (-1 / (((c : ℂ) + t * Complex.I) - 1)) * z)
                      (zetaLaplaceTransform_rightOnePoleProjectionKernel_verticalSlice_eq_fourier
                        f.toZetaTestFunction' c t))
            let hfull :
                (∫ t : ℝ,
                    (-1 / (((c : ℂ) + t * Complex.I) - 1)) *
                      zetaLaplaceTransform f.toZetaTestFunction'
                        (((c : ℂ) + t * Complex.I) - 1 / 2)) =
                  (∫ t : ℝ,
                    (-1 / (((c : ℂ) + t * Complex.I) - 1)) *
                      (∫ x : ℝ,
                        zetaLaplaceTransform_rightOnePoleProjectionKernel f.toZetaTestFunction' x *
                          Complex.exp
                            (Complex.I * (t : ℂ) * (x : ℂ)) *
                          Complex.exp (((c - 1 : ℝ) : ℂ) * (x : ℂ)))) :=
                integral_congr_ae
                  (Eventually.of_forall
                    (fun t : ℝ =>
                      congrArg
                        (fun z : ℂ =>
                          (-1 / (((c : ℂ) + t * Complex.I) - 1)) * z)
                        (zetaLaplaceTransform_rightOnePoleProjectionKernel_verticalSlice_eq_fourier
                          f.toZetaTestFunction' c t)))
            Eq.subst
              (motive := fun finiteValue : ℂ =>
                ‖finiteValue -
                  (∫ t : ℝ,
                    (-1 / (((c : ℂ) + t * Complex.I) - 1)) *
                      zetaLaplaceTransform f.toZetaTestFunction'
                        (((c : ℂ) + t * Complex.I) - 1 / 2))‖
                  ≤ MR * (1 + ‖height u‖) ^ (-(2 : ℤ)))
              hfinite.symm
              (Eq.subst
                (motive := fun fullValue : ℂ =>
                  ‖(∫ t in Set.Icc (-(height u)) (height u),
                      (-1 / (((c : ℂ) + t * Complex.I) - 1)) *
                        (∫ x : ℝ,
                          zetaLaplaceTransform_rightOnePoleProjectionKernel f.toZetaTestFunction' x *
                            Complex.exp
                              (Complex.I * (t : ℂ) * (x : ℂ)) *
                            Complex.exp (((c - 1 : ℝ) : ℂ) * (x : ℂ)))) -
                    fullValue‖
                    ≤ MR * (1 + ‖height u‖) ^ (-(2 : ℤ)))
                hfull.symm
                hu))⟩

/-- Kernel-level Fourier-Cauchy multiplier estimate for the right one-pole
projection.

This is the analytic owner sink: after the vertical-line Laplace slice is
rewritten as the Fourier transform of
`zetaLaplaceTransform_rightOnePoleProjectionKernel`, the Cauchy multiplier
`((c - 1) + it)⁻¹` projects onto the negative time half-line with an
inverse-quadratic symmetric truncation tail. -/
theorem zetaLaplaceTransform_rightOnePoleProjectionKernel_fixedLineCauchyMultiplier_estimate
    (f : LFunctions.ZetaAdmissibleFunction) (c : ℝ) (hc : 1 < c)
    (height : ℝ → ℝ) (hcofinal : Tendsto height atTop atTop) :
    ∃ MR : ℝ,
      0 < MR ∧
        ∀ᶠ u in atTop,
          ‖(∫ t in Set.Icc (-(height u)) (height u),
              (-1 / (((c : ℂ) + t * Complex.I) - 1)) *
                zetaLaplaceTransform f.toZetaTestFunction'
                  (((c : ℂ) + t * Complex.I) - 1 / 2)) -
            zetaLaplaceTransform_rightOnePoleCauchyProjectionValue f.toZetaTestFunction' c‖
            ≤ MR * (1 + ‖height u‖) ^ (-(2 : ℤ)) := by
  match
    zetaLaplaceTransform_rightOnePoleProjectionKernel_truncationTail_inverseQuadratic
      f c hc height hcofinal
  with
  | ⟨MR, hMR_pos, hMR_eventual⟩ =>
      exact ⟨MR, hMR_pos,
        hMR_eventual.mono
          (fun u hu =>
            let hvalue :
                (∫ t : ℝ,
                    (-1 / (((c : ℂ) + t * Complex.I) - 1)) *
                      zetaLaplaceTransform f.toZetaTestFunction'
                        (((c : ℂ) + t * Complex.I) - 1 / 2)) =
                  zetaLaplaceTransform_rightOnePoleCauchyProjectionValue f.toZetaTestFunction' c :=
                zetaLaplaceTransform_rightOnePoleProjectionKernel_fullLineCauchyValue
                  f.toZetaTestFunction' c hc
            Eq.subst
              (motive := fun z : ℂ =>
                ‖(∫ t in Set.Icc (-(height u)) (height u),
                    (-1 / (((c : ℂ) + t * Complex.I) - 1)) *
                      zetaLaplaceTransform f.toZetaTestFunction'
                        (((c : ℂ) + t * Complex.I) - 1 / 2)) -
                  z‖
                  ≤ MR * (1 + ‖height u‖) ^ (-(2 : ℤ)))
              hvalue
              hu)⟩

/-- Fixed-line Fourier-Cauchy projection theorem for compactly supported
logarithmic test functions.

This is the transform-calculus owner theorem: the symmetric truncations of the
right half-plane Cauchy multiplier on the fixed line converge to the one-sided
time projection with inverse-quadratic tail. -/
theorem zetaLaplaceTransform_fixedLine_rightOnePoleCauchyProjection_eventual_inverseQuadratic_to_value
    (f : LFunctions.ZetaAdmissibleFunction) (c : ℝ) (hc : 1 < c)
    (height : ℝ → ℝ) (hcofinal : Tendsto height atTop atTop) :
    ∃ MR : ℝ,
      0 < MR ∧
        ∀ᶠ u in atTop,
          ‖(∫ t in Set.Icc (-(height u)) (height u),
              (-1 / (((c : ℂ) + t * Complex.I) - 1)) *
                zetaLaplaceTransform f.toZetaTestFunction'
                  (((c : ℂ) + t * Complex.I) - 1 / 2)) -
            zetaLaplaceTransform_rightOnePoleCauchyProjectionValue f.toZetaTestFunction' c‖
            ≤ MR * (1 + ‖height u‖) ^ (-(2 : ℤ)) := by
  exact
    zetaLaplaceTransform_rightOnePoleProjectionKernel_fixedLineCauchyMultiplier_estimate
      f c hc height hcofinal

end FixedLineCauchyProjection

end
end Boundary
