import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaTransformCalculus.ZetaTransformCalculusBase.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaAdmissibleSpectralInterpolation.ZetaAdmissiblePaleyWiener.IteratedOscillatoryKernel.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaZeroTail.ZetaZeroMultiplicitySummability.ZetaZeroMultiplicityCounting.ZetaCompletedZeroJensen.ZetaEntireJensen.EntireJensenFormula.ZeroFreePrimitive.RadialFTC.Owner
import Mathlib.Analysis.Fourier.Inversion
import Mathlib.Data.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Integrals
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.SetIntegral

/-!
# Fixed-line Cauchy projection kernel layer

This split owner file contains the initial fixed-line kernel definitions and
pointwise decay estimates from the Cauchy projection owner chain.
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
  ∫ x in Set.Ici (0 : ℝ),
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

/-- Quadratic decay of the Fourier transform of the exponentially weighted
smooth compactly supported kernel on the fixed right line. -/
noncomputable def fixedRightLine_weightedKernel_admissibleFunction
    (K : ℝ → ℂ) (hK_cont : Continuous K) (hK_compact : HasCompactSupport K)
    (hK_smooth : ContDiff ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) K) :
    LFunctions.ZetaAdmissibleFunction where
  toZetaTestFunction :=
    CompactlySupportedContinuousMap.mk
      (ContinuousMap.mk K hK_cont)
      hK_compact
  smooth := hK_smooth

/-- The weighted fixed-line Fourier kernel is the Laplace transform of the
packaged admissible kernel on the vertical line `c - 1 + it`. -/
theorem fixedRightLine_weightedKernel_fourierIntegral_eq_laplace
    (K : ℝ → ℂ) (hK_cont : Continuous K) (hK_compact : HasCompactSupport K)
    (hK_smooth : ContDiff ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) K)
    (c t : ℝ) :
    (∫ x : ℝ,
        K x *
          Complex.exp
            (Complex.I * (t : ℂ) * (x : ℂ)) *
          Complex.exp (((c - 1 : ℝ) : ℂ) * (x : ℂ))) =
      zetaLaplaceTransform
        (fixedRightLine_weightedKernel_admissibleFunction
          K hK_cont hK_compact hK_smooth).toZetaTestFunction'
        (((c - 1 : ℝ) : ℂ) + t * Complex.I) := by
  unfold zetaLaplaceTransform
  exact
    (integral_congr_ae
      (Eventually.of_forall
        (fun x : ℝ =>
          calc
            K x *
                Complex.exp
                  (Complex.I * (t : ℂ) * (x : ℂ)) *
                Complex.exp (((c - 1 : ℝ) : ℂ) * (x : ℂ))
                =
                K x *
                  (Complex.exp
                    (Complex.I * (t : ℂ) * (x : ℂ)) *
                  Complex.exp (((c - 1 : ℝ) : ℂ) * (x : ℂ))) := by
                  exact mul_assoc (K x)
                    (Complex.exp (Complex.I * (t : ℂ) * (x : ℂ)))
                    (Complex.exp (((c - 1 : ℝ) : ℂ) * (x : ℂ)))
            _ =
                K x *
                  Complex.exp
                    (Complex.I * (t : ℂ) * (x : ℂ) +
                      ((c - 1 : ℝ) : ℂ) * (x : ℂ)) := by
                  exact congrArg (fun z : ℂ => K x * z)
                    ((Complex.exp_add
                      (Complex.I * (t : ℂ) * (x : ℂ))
                      (((c - 1 : ℝ) : ℂ) * (x : ℂ))).symm)
            _ =
                K x *
                  Complex.exp
                    ((((c - 1 : ℝ) : ℂ) + t * Complex.I) * (x : ℂ)) := by
                  exact congrArg (fun z : ℂ => K x * Complex.exp z)
                    (calc
                      Complex.I * (t : ℂ) * (x : ℂ) +
                          ((c - 1 : ℝ) : ℂ) * (x : ℂ)
                          =
                          ((t : ℂ) * Complex.I) * (x : ℂ) +
                            ((c - 1 : ℝ) : ℂ) * (x : ℂ) := by
                          exact congrArg
                            (fun z : ℂ => z * (x : ℂ) +
                              ((c - 1 : ℝ) : ℂ) * (x : ℂ))
                            (mul_comm Complex.I (t : ℂ))
                      _ =
                          (((t : ℂ) * Complex.I) +
                            ((c - 1 : ℝ) : ℂ)) * (x : ℂ) := by
                          exact (add_mul
                            ((t : ℂ) * Complex.I)
                            (((c - 1 : ℝ) : ℂ))
                            (x : ℂ)).symm
                      _ =
                          (((c - 1 : ℝ) : ℂ) +
                            (t : ℂ) * Complex.I) * (x : ℂ) := by
                          exact congrArg (fun z : ℂ => z * (x : ℂ))
                            (add_comm ((t : ℂ) * Complex.I)
                              (((c - 1 : ℝ) : ℂ)))
                      _ =
                          (((c - 1 : ℝ) : ℂ) + t * Complex.I) *
                            (x : ℂ) := by
                          rfl))))

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
  let f : LFunctions.ZetaAdmissibleFunction :=
    fixedRightLine_weightedKernel_admissibleFunction
      K hK_cont hK_compact hK_smooth
  match LFunctions.zetaLaplaceTransform_verticalStripRapidDecay_of_compactSupport_smooth
      f (c - 1) (c - 1) 2 with
  | ⟨B, hBpos, hBbound⟩ =>
      exact ⟨B, hBpos, fun t : ℝ =>
        let z : ℂ := (((c - 1 : ℝ) : ℂ) + t * Complex.I)
        let hz_re_left : c - 1 ≤ z.re := by
          calc
            c - 1 ≤ c - 1 := le_rfl
            _ = z.re := by
              exact
                (calc
                  z.re =
                      (((c - 1 : ℝ) : ℂ).re + (t * Complex.I).re) := by
                      exact Complex.add_re (((c - 1 : ℝ) : ℂ)) (t * Complex.I)
                  _ = (c - 1) + (t * Complex.I).re := by
                      exact congrArg (fun u : ℝ => u + (t * Complex.I).re)
                        (Complex.ofReal_re (c - 1))
                  _ = (c - 1) + -((t : ℂ).im) := by
                      exact congrArg (fun u : ℝ => (c - 1) + u)
                        (Complex.mul_I_re (t : ℂ))
                  _ = (c - 1) + -0 := by
                      exact congrArg (fun u : ℝ => (c - 1) + -u)
                        (Complex.ofReal_im t)
                  _ = (c - 1) + 0 := by
                      exact congrArg (fun u : ℝ => (c - 1) + u)
                        (neg_zero : -(0 : ℝ) = 0)
                  _ = c - 1 := add_zero (c - 1)).symm
        let hz_re_right : z.re ≤ c - 1 := by
          calc
            z.re = c - 1 := by
              calc
                z.re =
                    (((c - 1 : ℝ) : ℂ).re + (t * Complex.I).re) := by
                    exact Complex.add_re (((c - 1 : ℝ) : ℂ)) (t * Complex.I)
                _ = (c - 1) + (t * Complex.I).re := by
                    exact congrArg (fun u : ℝ => u + (t * Complex.I).re)
                      (Complex.ofReal_re (c - 1))
                _ = (c - 1) + -((t : ℂ).im) := by
                    exact congrArg (fun u : ℝ => (c - 1) + u)
                      (Complex.mul_I_re (t : ℂ))
                _ = (c - 1) + -0 := by
                    exact congrArg (fun u : ℝ => (c - 1) + -u)
                      (Complex.ofReal_im t)
                _ = (c - 1) + 0 := by
                    exact congrArg (fun u : ℝ => (c - 1) + u)
                      (neg_zero : -(0 : ℝ) = 0)
                _ = c - 1 := add_zero (c - 1)
            _ ≤ c - 1 := le_rfl
        let hz_im_norm : ‖z.im‖ = ‖t‖ := by
          exact congrArg norm
            (calc
              z.im =
                  (((c - 1 : ℝ) : ℂ).im + (t * Complex.I).im) := by
                  exact Complex.add_im (((c - 1 : ℝ) : ℂ)) (t * Complex.I)
              _ = 0 + (t * Complex.I).im := by
                  exact congrArg (fun u : ℝ => u + (t * Complex.I).im)
                    (Complex.ofReal_im (c - 1))
              _ = 0 + t := by
                  exact congrArg (fun u : ℝ => 0 + u)
                    (Complex.mul_I_im (t : ℂ))
              _ = t := zero_add t)
        let hdecay :
            ‖zetaLaplaceTransform f.toZetaTestFunction' z‖
              ≤ B * (1 + ‖z.im‖) ^ (-(2 : ℤ)) :=
          hBbound z hz_re_left hz_re_right
        let htransport :
            ‖(∫ x : ℝ,
                K x *
                  Complex.exp
                    (Complex.I * (t : ℂ) * (x : ℂ)) *
                  Complex.exp (((c - 1 : ℝ) : ℂ) * (x : ℂ)))‖ =
              ‖zetaLaplaceTransform f.toZetaTestFunction' z‖ := by
          exact congrArg norm
            (fixedRightLine_weightedKernel_fourierIntegral_eq_laplace
              K hK_cont hK_compact hK_smooth c t)
        Eq.subst
          (motive := fun u : ℝ =>
            ‖(∫ x : ℝ,
                K x *
                  Complex.exp
                    (Complex.I * (t : ℂ) * (x : ℂ)) *
                  Complex.exp (((c - 1 : ℝ) : ℂ) * (x : ℂ)))‖
              ≤ B * (1 + u) ^ (-(2 : ℤ)))
          hz_im_norm
          (Eq.subst
            (motive := fun u : ℝ =>
              u ≤ B * (1 + ‖z.im‖) ^ (-(2 : ℤ)))
            htransport.symm
            hdecay)⟩

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
          exact congrArg _root_.abs hIm.symm
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
          exact (_root_.abs_of_nonneg hRateNonnegative).symm
    _ = |((((c : ℂ) + t * Complex.I) - 1).re)| := by
          exact congrArg _root_.abs hRe.symm
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
        (hRealPart.symm.trans
          ((congrArg Complex.re hZero).trans Complex.zero_re))

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
            (inv_anti₀ hRatePos hRateNorm)
            ((inv_mul_le_one₀ hDenomPos).mpr hFreq)
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

end FixedLineCauchyProjection

end
end Boundary
