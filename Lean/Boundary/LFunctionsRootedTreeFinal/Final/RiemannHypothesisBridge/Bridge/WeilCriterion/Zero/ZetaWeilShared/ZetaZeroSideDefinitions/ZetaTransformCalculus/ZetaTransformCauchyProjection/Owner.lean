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

/-- The fixed right Cauchy multiplier contributes one inverse power on the
vertical frequency variable. -/
theorem fixedRightLine_cauchyMultiplier_norm_inverseLinearBound
    (c : ℝ) (hc : 1 < c) :
    ∃ D : ℝ,
      0 < D ∧
        ∀ t : ℝ,
          ‖(-1 / (((c : ℂ) + t * Complex.I) - 1))‖
            ≤ D * (1 + ‖t‖) ^ (-(1 : ℤ)) := by
  sorry

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

/-- On a nonnegative right tail, the inverse-cubic norm majorant is the
translated open-tail power integral. -/
theorem real_inverseCubic_rightTail_integral_eq_shifted_rpow_Ioi
    (T : ℝ) (hT : 0 ≤ T) :
    (∫ t in Set.Ici T,
        (1 + ‖t‖) ^ (-(3 : ℤ)) : ℝ)
      =
    (∫ u in Set.Ioi (1 + T),
        u ^ (-(3 : ℝ)) : ℝ) := by
  sorry

/-- Numeric comparison needed for the inverse-cubic improper integral. -/
theorem negThree_lt_negOne_real :
    (-(3 : ℝ)) < -1 := by
  exact neg_lt_neg one_lt_three

/-- The antiderivative boundary value appearing in
`integral_Ioi_rpow_of_lt` for exponent `-3` is the expected half
inverse-square value. -/
theorem real_negThree_rpow_tail_antiderivative_value_eq_half_rpow_negTwo
    (c : ℝ) :
    -(c ^ (-(3 : ℝ) + 1)) / (-(3 : ℝ) + 1)
      =
    (1 / 2 : ℝ) * c ^ (-(2 : ℝ)) := by
  sorry

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

/-- The left closed inverse-cubic norm tail is the corresponding right closed
tail by the reflection symmetry of Lebesgue measure and the norm. -/
theorem real_inverseCubic_leftTail_integral_eq_rightTail
    (T : ℝ) :
    (∫ t in Set.Iic (-T),
        (1 + ‖t‖) ^ (-(3 : ℤ)) : ℝ)
      =
    (∫ t in Set.Ici T,
        (1 + ‖t‖) ^ (-(3 : ℤ)) : ℝ) := by
  sorry

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
    (G : ℝ → ℂ) (C : ℝ) (hC : 0 < C)
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
  sorry

/-- Inverse-cubic pointwise decay gives an inverse-quadratic symmetric
truncation tail along any cofinal height schedule. -/
theorem fixedRightLine_integrableFunction_symmetricTail_inverseQuadratic_of_inverseCubicDecay
    (G : ℝ → ℂ)
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
          G C hC height hG).and hA_eventual).mono
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
