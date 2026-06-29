import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaTransformCalculus.ZetaTransformCalculusBase.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaAdmissibleSpectralInterpolation.ZetaAdmissiblePaleyWiener.IteratedOscillatoryKernel.Owner
import Mathlib.Analysis.Fourier.Inversion
import Mathlib.Data.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
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
                  _ = (c - 1) + 0 := by
                      exact congrArg (fun u : ℝ => (c - 1) + u)
                        (Complex.mul_I_re (t : ℂ))
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
                _ = (c - 1) + 0 := by
                    exact congrArg (fun u : ℝ => (c - 1) + u)
                      (Complex.mul_I_re (t : ℂ))
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

/-- A cofinal height schedule sends the Japanese bracket to infinity. -/
theorem cofinalHeight_one_add_norm_tendsto_atTop
    (height : ℝ → ℝ) (hcofinal : Tendsto height atTop atTop) :
    Tendsto (fun u : ℝ => (1 + ‖height u‖ : ℝ)) atTop atTop :=
  tendsto_atTop.2
    (fun A : ℝ =>
      (hcofinal.eventually_ge_atTop A).mono
        (fun u hu =>
          le_trans hu
            (le_trans
              (Real.le_norm_self (height u))
              (le_add_of_nonneg_left zero_le_one))))

/-- Inverse-square decay along a cofinal height schedule tends to zero. -/
theorem cofinalHeight_one_add_norm_inverseQuadratic_tendsto_zero
    (height : ℝ → ℝ) (hcofinal : Tendsto height atTop atTop) :
    Tendsto
      (fun u : ℝ => (1 + ‖height u‖) ^ (-(2 : ℤ)) : ℝ)
      atTop
      (𝓝 0) :=
  (tendsto_zpow_atTop_zero (show (-(2 : ℤ)) < 0 by exact Int.negSucc_lt_zero 1)).comp
    (cofinalHeight_one_add_norm_tendsto_atTop height hcofinal)

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

/-- Inverse-quadratic symmetric tail control identifies the full-line integral
as the limit of symmetric truncations. -/
theorem fixedRightLine_integrableFunction_symmetricTruncation_tendsto_fullLine_of_inverseQuadraticTail
    (G : ℝ → ℂ) (height : ℝ → ℝ)
    (hcofinal : Tendsto height atTop atTop)
    (htail :
      ∃ MR : ℝ,
        0 < MR ∧
          ∀ᶠ u in atTop,
            ‖(∫ t in Set.Icc (-(height u)) (height u), G t) -
                (∫ t : ℝ, G t)‖
              ≤ MR * (1 + ‖height u‖) ^ (-(2 : ℤ))) :
    Tendsto
      (fun u : ℝ =>
        ∫ t in Set.Icc (-(height u)) (height u), G t)
      atTop
      (𝓝 (∫ t : ℝ, G t)) := by
  match htail with
  | ⟨MR, hMR_pos, hMR_eventual⟩ =>
      have hMR_nonneg : 0 ≤ MR :=
        le_of_lt hMR_pos
      have hdecay :
          Tendsto
            (fun u : ℝ =>
              MR * (1 + ‖height u‖) ^ (-(2 : ℤ)))
            atTop
            (𝓝 (MR * 0)) :=
        tendsto_const_nhds.mul
          (cofinalHeight_one_add_norm_inverseQuadratic_tendsto_zero
            height hcofinal)
      have hzero :
          MR * (0 : ℝ) = 0 :=
        mul_zero MR
      have hmajorant :
          Tendsto
            (fun u : ℝ =>
              MR * (1 + ‖height u‖) ^ (-(2 : ℤ)))
            atTop
            (𝓝 0) :=
        hzero ▸ hdecay
      exact
        tendsto_iff_norm_sub_tendsto_zero.2
          (squeeze_zero_norm' hMR_eventual hmajorant)

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

/-- Symmetric truncations of the smooth fixed-line Fourier-Cauchy multiplier
converge to the full-line ordinary integral. -/
theorem fixedRightLine_fourierCauchy_symmetricTruncation_tendsto_fullLine
    (K : ℝ → ℂ) (hK_cont : Continuous K) (hK_compact : HasCompactSupport K)
    (hK_smooth : ContDiff ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) K)
    (c : ℝ) (hc : 1 < c) :
    Tendsto
      (fun T : ℝ =>
        ∫ t in Set.Icc (-T) T,
          (-1 / (((c : ℂ) + t * Complex.I) - 1)) *
            (∫ x : ℝ,
              K x *
                Complex.exp
                  (Complex.I * (t : ℂ) * (x : ℂ)) *
                Complex.exp (((c - 1 : ℝ) : ℂ) * (x : ℂ))))
      atTop
      (𝓝
        (∫ t : ℝ,
          (-1 / (((c : ℂ) + t * Complex.I) - 1)) *
            (∫ x : ℝ,
              K x *
                Complex.exp
                  (Complex.I * (t : ℂ) * (x : ℂ)) *
                Complex.exp (((c - 1 : ℝ) : ℂ) * (x : ℂ))))) := by
  exact
    fixedRightLine_integrableFunction_symmetricTruncation_tendsto_fullLine_of_inverseQuadraticTail
      (fun t : ℝ =>
        (-1 / (((c : ℂ) + t * Complex.I) - 1)) *
          (∫ x : ℝ,
            K x *
              Complex.exp
                (Complex.I * (t : ℂ) * (x : ℂ)) *
              Complex.exp (((c - 1 : ℝ) : ℂ) * (x : ℂ))))
      (fun T : ℝ => T)
      tendsto_id
      (fixedRightLine_fourierCauchy_truncationTail_inverseQuadratic
        K hK_cont hK_compact hK_smooth c hc
        (fun T : ℝ => T)
        tendsto_id)

/-- The scalar Cauchy kernel indicator integral is the one-sided projection
integral. -/
theorem fixedRightLine_fourierCauchy_scalarKernelIntegral_eq_oneSidedProjection
    (K : ℝ → ℂ) :
    (∫ x : ℝ,
        K x *
          Set.indicator (Set.Ici (0 : ℝ))
            (fun _ : ℝ => (-2 * (Real.pi : ℂ))) x) =
      ∫ x in Set.Ici (0 : ℝ),
        (-2 * (Real.pi : ℂ)) * K x := by
  calc
    (∫ x : ℝ,
        K x *
          Set.indicator (Set.Ici (0 : ℝ))
            (fun _ : ℝ => (-2 * (Real.pi : ℂ))) x)
        =
        ∫ x : ℝ,
          Set.indicator (Set.Ici (0 : ℝ))
            (fun y : ℝ => (-2 * (Real.pi : ℂ)) * K y) x := by
          exact integral_congr_ae
            (Eventually.of_forall
              (fun x : ℝ =>
                if hx : x ∈ Set.Ici (0 : ℝ) then
                  calc
                    K x *
                        Set.indicator (Set.Ici (0 : ℝ))
                          (fun _ : ℝ => (-2 * (Real.pi : ℂ))) x
                        = K x * (-2 * (Real.pi : ℂ)) := by
                          exact congrArg
                            (fun z : ℂ => K x * z)
                            (indicator_of_mem hx
                              (fun _ : ℝ => (-2 * (Real.pi : ℂ))))
                    _ = (-2 * (Real.pi : ℂ)) * K x := by
                          exact mul_comm (K x) (-2 * (Real.pi : ℂ))
                    _ =
                        Set.indicator (Set.Ici (0 : ℝ))
                          (fun y : ℝ => (-2 * (Real.pi : ℂ)) * K y) x := by
                          exact (indicator_of_mem hx
                            (fun y : ℝ => (-2 * (Real.pi : ℂ)) * K y)).symm
                else
                  calc
                    K x *
                        Set.indicator (Set.Ici (0 : ℝ))
                          (fun _ : ℝ => (-2 * (Real.pi : ℂ))) x
                        = K x * 0 := by
                          exact congrArg
                            (fun z : ℂ => K x * z)
                            (indicator_of_not_mem hx
                              (fun _ : ℝ => (-2 * (Real.pi : ℂ))))
                    _ = 0 := by
                          exact mul_zero (K x)
                    _ =
                        Set.indicator (Set.Ici (0 : ℝ))
                          (fun y : ℝ => (-2 * (Real.pi : ℂ)) * K y) x := by
                          exact (indicator_of_not_mem hx
                            (fun y : ℝ => (-2 * (Real.pi : ℂ)) * K y)).symm))
    _ =
        ∫ x in Set.Ici (0 : ℝ),
          (-2 * (Real.pi : ℂ)) * K x := by
          exact integral_indicator measurableSet_Ici

/-- Product integrability for the finite-window fixed-right-line Cauchy kernel. -/
theorem fixedRightLine_fourierCauchy_symmetricWindow_productIntegrable
    (K : ℝ → ℂ) (hK_cont : Continuous K) (hK_compact : HasCompactSupport K)
    (hK_smooth : ContDiff ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) K)
    (c : ℝ) (hc : 1 < c) (T : ℝ) :
    IntegrableOn
      (fun p : ℝ × ℝ =>
        (-1 / (((c : ℂ) + p.1 * Complex.I) - 1)) *
          K p.2 *
          Complex.exp
            (Complex.I * (p.1 : ℂ) * (p.2 : ℂ)) *
          Complex.exp (((c - 1 : ℝ) : ℂ) * (p.2 : ℂ)))
      (Set.Icc (-T) T ×ˢ Set.univ) := by
  let F : ℝ × ℝ → ℂ :=
    fun p : ℝ × ℝ =>
      (-1 / (((c : ℂ) + p.1 * Complex.I) - 1)) *
        K p.2 *
        Complex.exp
          (Complex.I * (p.1 : ℂ) * (p.2 : ℂ)) *
        Complex.exp (((c - 1 : ℝ) : ℂ) * (p.2 : ℂ))
  have hden :
      Continuous
        (fun p : ℝ × ℝ =>
          (((c : ℂ) + p.1 * Complex.I) - 1)) :=
    (continuous_const.add
      ((Complex.continuous_ofReal.comp continuous_fst).mul continuous_const)).sub
      continuous_const
  have hden_ne :
      ∀ p : ℝ × ℝ,
        (((c : ℂ) + p.1 * Complex.I) - 1) ≠ 0 :=
    fun p : ℝ × ℝ =>
      fixedRightLine_cauchyDenominator_ne_zero c p.1 hc
  have hscalar :
      Continuous
        (fun p : ℝ × ℝ =>
          -1 / (((c : ℂ) + p.1 * Complex.I) - 1)) :=
    continuous_const.div hden hden_ne
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
          ((c - 1 : ℝ) : ℂ) * (p.2 : ℂ)) :=
    continuous_const.mul
      (Complex.continuous_ofReal.comp continuous_snd)
  have hF_cont : Continuous F :=
    ((hscalar.mul hK_pair).mul
      (Complex.continuous_exp.comp hphase)).mul
        (Complex.continuous_exp.comp hweight)
  have hcompact :
      IsCompact (Set.Icc (-T) T ×ˢ tsupport K) :=
    isCompact_Icc.prod hK_compact
  have hF_compact :
      IntegrableOn F (Set.Icc (-T) T ×ˢ tsupport K) :=
    hF_cont.continuousOn.integrableOn_compact hcompact
  exact
    hF_compact.of_forall_diff_eq_zero
      (measurableSet_Icc.prod measurableSet_univ)
      (fun p hp =>
        let hnot :
            p.2 ∉ tsupport K :=
          fun hp_support =>
            hp.2 ⟨hp.1.1, hp_support⟩
        calc
          F p =
              (-1 / (((c : ℂ) + p.1 * Complex.I) - 1)) *
                K p.2 *
                Complex.exp
                  (Complex.I * (p.1 : ℂ) * (p.2 : ℂ)) *
                Complex.exp (((c - 1 : ℝ) : ℂ) * (p.2 : ℂ)) := by
                exact rfl
          _ =
              (-1 / (((c : ℂ) + p.1 * Complex.I) - 1)) *
                0 *
                Complex.exp
                  (Complex.I * (p.1 : ℂ) * (p.2 : ℂ)) *
                Complex.exp (((c - 1 : ℝ) : ℂ) * (p.2 : ℂ)) := by
                exact congrArg
                  (fun z : ℂ =>
                    (-1 / (((c : ℂ) + p.1 * Complex.I) - 1)) *
                      z *
                      Complex.exp
                        (Complex.I * (p.1 : ℂ) * (p.2 : ℂ)) *
                      Complex.exp (((c - 1 : ℝ) : ℂ) * (p.2 : ℂ)))
                  (image_eq_zero_of_nmem_tsupport hnot)
          _ =
              0 *
                Complex.exp
                  (Complex.I * (p.1 : ℂ) * (p.2 : ℂ)) *
                Complex.exp (((c - 1 : ℝ) : ℂ) * (p.2 : ℂ)) := by
                exact congrArg
                  (fun z : ℂ =>
                    z *
                      Complex.exp
                        (Complex.I * (p.1 : ℂ) * (p.2 : ℂ)) *
                      Complex.exp (((c - 1 : ℝ) : ℂ) * (p.2 : ℂ)))
                  (mul_zero
                    (-1 / (((c : ℂ) + p.1 * Complex.I) - 1)))
          _ =
              0 *
                Complex.exp (((c - 1 : ℝ) : ℂ) * (p.2 : ℂ)) := by
                exact congrArg
                  (fun z : ℂ =>
                    z *
                      Complex.exp (((c - 1 : ℝ) : ℂ) * (p.2 : ℂ)))
                  (zero_mul
                    (Complex.exp
                      (Complex.I * (p.1 : ℂ) * (p.2 : ℂ))))
          _ = 0 := by
                exact zero_mul
                  (Complex.exp (((c - 1 : ℝ) : ℂ) * (p.2 : ℂ)))

/-- Standard Fubini form of the finite-window product Cauchy integral. -/
theorem fixedRightLine_fourierCauchy_symmetricWindow_productIntegral_eq_iterated
    (K : ℝ → ℂ) (hK_cont : Continuous K) (hK_compact : HasCompactSupport K)
    (hK_smooth : ContDiff ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) K)
    (c : ℝ) (hc : 1 < c) (T : ℝ) :
    (∫ p in Set.Icc (-T) T ×ˢ Set.univ,
        (-1 / (((c : ℂ) + p.1 * Complex.I) - 1)) *
          K p.2 *
          Complex.exp
            (Complex.I * (p.1 : ℂ) * (p.2 : ℂ)) *
          Complex.exp (((c - 1 : ℝ) : ℂ) * (p.2 : ℂ))) =
      ∫ t in Set.Icc (-T) T,
        ∫ x : ℝ,
          (-1 / (((c : ℂ) + t * Complex.I) - 1)) *
            K x *
            Complex.exp
              (Complex.I * (t : ℂ) * (x : ℂ)) *
            Complex.exp (((c - 1 : ℝ) : ℂ) * (x : ℂ)) := by
  exact
    setIntegral_prod
      (fun p : ℝ × ℝ =>
        (-1 / (((c : ℂ) + p.1 * Complex.I) - 1)) *
          K p.2 *
          Complex.exp
            (Complex.I * (p.1 : ℂ) * (p.2 : ℂ)) *
          Complex.exp (((c - 1 : ℝ) : ℂ) * (p.2 : ℂ)))
      (fixedRightLine_fourierCauchy_symmetricWindow_productIntegrable
        K hK_cont hK_compact hK_smooth c hc T)

/-- Pointwise reassociation for pulling the fixed Cauchy scalar outside the
inner time-side integral. -/
theorem fixedRightLine_outerScalar_integrand_reassoc
    (K : ℝ → ℂ) (c t x : ℝ) :
    (-1 / (((c : ℂ) + t * Complex.I) - 1)) *
        (K x *
          Complex.exp
            (Complex.I * (t : ℂ) * (x : ℂ)) *
          Complex.exp (((c - 1 : ℝ) : ℂ) * (x : ℂ))) =
      (-1 / (((c : ℂ) + t * Complex.I) - 1)) *
        K x *
        Complex.exp
          (Complex.I * (t : ℂ) * (x : ℂ)) *
        Complex.exp (((c - 1 : ℝ) : ℂ) * (x : ℂ)) := by
  calc
    (-1 / (((c : ℂ) + t * Complex.I) - 1)) *
        (K x *
          Complex.exp
            (Complex.I * (t : ℂ) * (x : ℂ)) *
          Complex.exp (((c - 1 : ℝ) : ℂ) * (x : ℂ)))
        =
        ((-1 / (((c : ℂ) + t * Complex.I) - 1)) *
          (K x *
            Complex.exp
              (Complex.I * (t : ℂ) * (x : ℂ)))) *
          Complex.exp (((c - 1 : ℝ) : ℂ) * (x : ℂ)) := by
          exact mul_assoc
            (-1 / (((c : ℂ) + t * Complex.I) - 1))
            (K x *
              Complex.exp
                (Complex.I * (t : ℂ) * (x : ℂ)))
            (Complex.exp (((c - 1 : ℝ) : ℂ) * (x : ℂ)))
    _ =
        (((-1 / (((c : ℂ) + t * Complex.I) - 1)) * K x) *
          Complex.exp
            (Complex.I * (t : ℂ) * (x : ℂ))) *
          Complex.exp (((c - 1 : ℝ) : ℂ) * (x : ℂ)) := by
          exact congrArg
            (fun z : ℂ =>
              z *
                Complex.exp (((c - 1 : ℝ) : ℂ) * (x : ℂ)))
            (mul_assoc
              (-1 / (((c : ℂ) + t * Complex.I) - 1))
              (K x)
              (Complex.exp
                (Complex.I * (t : ℂ) * (x : ℂ))))
    _ =
        ((-1 / (((c : ℂ) + t * Complex.I) - 1)) * K x) *
          Complex.exp
            (Complex.I * (t : ℂ) * (x : ℂ)) *
          Complex.exp (((c - 1 : ℝ) : ℂ) * (x : ℂ)) := by
          exact (mul_assoc
            ((-1 / (((c : ℂ) + t * Complex.I) - 1)) * K x)
            (Complex.exp
              (Complex.I * (t : ℂ) * (x : ℂ)))
            (Complex.exp (((c - 1 : ℝ) : ℂ) * (x : ℂ)))).symm

/-- The finite-window iterated product integral pulls the Cauchy scalar outside
the inner time-side integral. -/
theorem fixedRightLine_fourierCauchy_symmetricWindow_iterated_eq_outerScalarIntegral
    (K : ℝ → ℂ) (hK_cont : Continuous K) (hK_compact : HasCompactSupport K)
    (hK_smooth : ContDiff ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) K)
    (c : ℝ) (hc : 1 < c) (T : ℝ) :
    (∫ t in Set.Icc (-T) T,
        ∫ x : ℝ,
          (-1 / (((c : ℂ) + t * Complex.I) - 1)) *
            K x *
            Complex.exp
              (Complex.I * (t : ℂ) * (x : ℂ)) *
            Complex.exp (((c - 1 : ℝ) : ℂ) * (x : ℂ))) =
      ∫ t in Set.Icc (-T) T,
        (-1 / (((c : ℂ) + t * Complex.I) - 1)) *
          (∫ x : ℝ,
            K x *
            Complex.exp
              (Complex.I * (t : ℂ) * (x : ℂ)) *
            Complex.exp (((c - 1 : ℝ) : ℂ) * (x : ℂ))) := by
  exact
    integral_congr_ae
      (Eventually.of_forall
        (fun t : ℝ =>
          calc
            (∫ x : ℝ,
              (-1 / (((c : ℂ) + t * Complex.I) - 1)) *
                K x *
                Complex.exp
                  (Complex.I * (t : ℂ) * (x : ℂ)) *
                Complex.exp (((c - 1 : ℝ) : ℂ) * (x : ℂ)))
                =
                ∫ x : ℝ,
                  (-1 / (((c : ℂ) + t * Complex.I) - 1)) *
                    (K x *
                      Complex.exp
                        (Complex.I * (t : ℂ) * (x : ℂ)) *
                      Complex.exp (((c - 1 : ℝ) : ℂ) * (x : ℂ))) := by
                  exact
                    integral_congr_ae
                      (Eventually.of_forall
                        (fun x : ℝ =>
                          (fixedRightLine_outerScalar_integrand_reassoc
                            K c t x).symm))
            _ =
                (-1 / (((c : ℂ) + t * Complex.I) - 1)) *
                  (∫ x : ℝ,
                    K x *
                      Complex.exp
                        (Complex.I * (t : ℂ) * (x : ℂ)) *
                      Complex.exp (((c - 1 : ℝ) : ℂ) * (x : ℂ))) := by
                  exact
                    integral_mul_left
                      (-1 / (((c : ℂ) + t * Complex.I) - 1))
                      (fun x : ℝ =>
                        K x *
                          Complex.exp
                            (Complex.I * (t : ℂ) * (x : ℂ)) *
                          Complex.exp (((c - 1 : ℝ) : ℂ) * (x : ℂ)))))

/-- The finite-window fixed-right-line Cauchy integral is the corresponding
product integral. -/
theorem fixedRightLine_fourierCauchy_symmetricWindow_eq_productIntegral
    (K : ℝ → ℂ) (hK_cont : Continuous K) (hK_compact : HasCompactSupport K)
    (hK_smooth : ContDiff ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) K)
    (c : ℝ) (hc : 1 < c) (T : ℝ) :
    (∫ t in Set.Icc (-T) T,
        (-1 / (((c : ℂ) + t * Complex.I) - 1)) *
          (∫ x : ℝ,
            K x *
              Complex.exp
                (Complex.I * (t : ℂ) * (x : ℂ)) *
              Complex.exp (((c - 1 : ℝ) : ℂ) * (x : ℂ)))) =
      ∫ p in Set.Icc (-T) T ×ˢ Set.univ,
        (-1 / (((c : ℂ) + p.1 * Complex.I) - 1)) *
          K p.2 *
          Complex.exp
            (Complex.I * (p.1 : ℂ) * (p.2 : ℂ)) *
          Complex.exp (((c - 1 : ℝ) : ℂ) * (p.2 : ℂ)) := by
  calc
    (∫ t in Set.Icc (-T) T,
        (-1 / (((c : ℂ) + t * Complex.I) - 1)) *
          (∫ x : ℝ,
            K x *
              Complex.exp
                (Complex.I * (t : ℂ) * (x : ℂ)) *
              Complex.exp (((c - 1 : ℝ) : ℂ) * (x : ℂ))))
        =
        ∫ t in Set.Icc (-T) T,
          ∫ x : ℝ,
            (-1 / (((c : ℂ) + t * Complex.I) - 1)) *
              K x *
              Complex.exp
                (Complex.I * (t : ℂ) * (x : ℂ)) *
              Complex.exp (((c - 1 : ℝ) : ℂ) * (x : ℂ)) := by
          exact
            (fixedRightLine_fourierCauchy_symmetricWindow_iterated_eq_outerScalarIntegral
              K hK_cont hK_compact hK_smooth c hc T).symm
    _ =
        ∫ p in Set.Icc (-T) T ×ˢ Set.univ,
          (-1 / (((c : ℂ) + p.1 * Complex.I) - 1)) *
            K p.2 *
            Complex.exp
              (Complex.I * (p.1 : ℂ) * (p.2 : ℂ)) *
            Complex.exp (((c - 1 : ℝ) : ℂ) * (p.2 : ℂ)) := by
          exact
            (fixedRightLine_fourierCauchy_symmetricWindow_productIntegral_eq_iterated
              K hK_cont hK_compact hK_smooth c hc T).symm

/-- Pointwise commutative reassociation for the scalar-window integrand. -/
theorem fixedRightLine_scalarWindow_constMul_integrand_reassoc
    (K : ℝ → ℂ) (c t x : ℝ) :
    K x *
        ((-1 / (((c : ℂ) + t * Complex.I) - 1)) *
          Complex.exp
            (Complex.I * (t : ℂ) * (x : ℂ)) *
          Complex.exp (((c - 1 : ℝ) : ℂ) * (x : ℂ))) =
      (-1 / (((c : ℂ) + t * Complex.I) - 1)) *
        K x *
        Complex.exp
          (Complex.I * (t : ℂ) * (x : ℂ)) *
        Complex.exp (((c - 1 : ℝ) : ℂ) * (x : ℂ)) := by
  calc
    K x *
        ((-1 / (((c : ℂ) + t * Complex.I) - 1)) *
          Complex.exp
            (Complex.I * (t : ℂ) * (x : ℂ)) *
          Complex.exp (((c - 1 : ℝ) : ℂ) * (x : ℂ)))
        =
        (K x *
          ((-1 / (((c : ℂ) + t * Complex.I) - 1)) *
            Complex.exp
              (Complex.I * (t : ℂ) * (x : ℂ)))) *
          Complex.exp (((c - 1 : ℝ) : ℂ) * (x : ℂ)) := by
          exact mul_assoc (K x)
            ((-1 / (((c : ℂ) + t * Complex.I) - 1)) *
              Complex.exp
                (Complex.I * (t : ℂ) * (x : ℂ)))
            (Complex.exp (((c - 1 : ℝ) : ℂ) * (x : ℂ)))
    _ =
        ((K x * (-1 / (((c : ℂ) + t * Complex.I) - 1))) *
          Complex.exp
            (Complex.I * (t : ℂ) * (x : ℂ))) *
          Complex.exp (((c - 1 : ℝ) : ℂ) * (x : ℂ)) := by
          exact congrArg
            (fun z : ℂ =>
              z *
                Complex.exp (((c - 1 : ℝ) : ℂ) * (x : ℂ)))
            (mul_assoc (K x)
              (-1 / (((c : ℂ) + t * Complex.I) - 1))
              (Complex.exp
                (Complex.I * (t : ℂ) * (x : ℂ))))
    _ =
        (((-1 / (((c : ℂ) + t * Complex.I) - 1)) * K x) *
          Complex.exp
            (Complex.I * (t : ℂ) * (x : ℂ))) *
          Complex.exp (((c - 1 : ℝ) : ℂ) * (x : ℂ)) := by
          exact congrArg
            (fun z : ℂ =>
              (z *
                Complex.exp
                  (Complex.I * (t : ℂ) * (x : ℂ))) *
                Complex.exp (((c - 1 : ℝ) : ℂ) * (x : ℂ)))
            (mul_comm (K x)
              (-1 / (((c : ℂ) + t * Complex.I) - 1)))
    _ =
        ((-1 / (((c : ℂ) + t * Complex.I) - 1)) * K x) *
          Complex.exp
            (Complex.I * (t : ℂ) * (x : ℂ)) *
          Complex.exp (((c - 1 : ℝ) : ℂ) * (x : ℂ)) := by
          exact (mul_assoc
            ((-1 / (((c : ℂ) + t * Complex.I) - 1)) * K x)
            (Complex.exp
              (Complex.I * (t : ℂ) * (x : ℂ)))
            (Complex.exp (((c - 1 : ℝ) : ℂ) * (x : ℂ)))).symm

/-- The scalar-window expression is the reversed iterated product integral. -/
theorem fixedRightLine_scalarWindowIntegral_eq_reversedIterated
    (K : ℝ → ℂ) (hK_cont : Continuous K) (hK_compact : HasCompactSupport K)
    (hK_smooth : ContDiff ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) K)
    (c : ℝ) (hc : 1 < c) (T : ℝ) :
    (∫ x : ℝ,
        K x *
          (∫ t in Set.Icc (-T) T,
            (-1 / (((c : ℂ) + t * Complex.I) - 1)) *
              Complex.exp
                (Complex.I * (t : ℂ) * (x : ℂ)) *
              Complex.exp (((c - 1 : ℝ) : ℂ) * (x : ℂ)))) =
      ∫ x : ℝ,
        ∫ t in Set.Icc (-T) T,
          (-1 / (((c : ℂ) + t * Complex.I) - 1)) *
            K x *
            Complex.exp
              (Complex.I * (t : ℂ) * (x : ℂ)) *
            Complex.exp (((c - 1 : ℝ) : ℂ) * (x : ℂ)) := by
  exact
    integral_congr_ae
      (Eventually.of_forall
        (fun x : ℝ =>
          calc
            K x *
                (∫ t in Set.Icc (-T) T,
                  (-1 / (((c : ℂ) + t * Complex.I) - 1)) *
                    Complex.exp
                      (Complex.I * (t : ℂ) * (x : ℂ)) *
                    Complex.exp (((c - 1 : ℝ) : ℂ) * (x : ℂ)))
                =
                ∫ t in Set.Icc (-T) T,
                  K x *
                    ((-1 / (((c : ℂ) + t * Complex.I) - 1)) *
                      Complex.exp
                        (Complex.I * (t : ℂ) * (x : ℂ)) *
                      Complex.exp (((c - 1 : ℝ) : ℂ) * (x : ℂ))) := by
                  exact
                    (integral_mul_left
                      (K x)
                      (fun t : ℝ =>
                        (-1 / (((c : ℂ) + t * Complex.I) - 1)) *
                          Complex.exp
                            (Complex.I * (t : ℂ) * (x : ℂ)) *
                          Complex.exp (((c - 1 : ℝ) : ℂ) * (x : ℂ)))).symm
            _ =
                ∫ t in Set.Icc (-T) T,
                  (-1 / (((c : ℂ) + t * Complex.I) - 1)) *
                    K x *
                    Complex.exp
                      (Complex.I * (t : ℂ) * (x : ℂ)) *
                    Complex.exp (((c - 1 : ℝ) : ℂ) * (x : ℂ)) := by
                  exact
                    integral_congr_ae
                      (Eventually.of_forall
                        (fun t : ℝ =>
                          fixedRightLine_scalarWindow_constMul_integrand_reassoc
                            K c t x))))

/-- Swapped-coordinate product integrability for the finite-window scalar
Cauchy kernel. -/
theorem fixedRightLine_scalarWindow_swappedProductIntegrable
    (K : ℝ → ℂ) (hK_cont : Continuous K) (hK_compact : HasCompactSupport K)
    (hK_smooth : ContDiff ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) K)
    (c : ℝ) (hc : 1 < c) (T : ℝ) :
    IntegrableOn
      (fun q : ℝ × ℝ =>
        (-1 / (((c : ℂ) + q.2 * Complex.I) - 1)) *
          K q.1 *
          Complex.exp
            (Complex.I * (q.2 : ℂ) * (q.1 : ℂ)) *
          Complex.exp (((c - 1 : ℝ) : ℂ) * (q.1 : ℂ)))
      (Set.univ ×ˢ Set.Icc (-T) T) := by
  let F : ℝ × ℝ → ℂ :=
    fun p : ℝ × ℝ =>
      (-1 / (((c : ℂ) + p.1 * Complex.I) - 1)) *
        K p.2 *
        Complex.exp
          (Complex.I * (p.1 : ℂ) * (p.2 : ℂ)) *
        Complex.exp (((c - 1 : ℝ) : ℂ) * (p.2 : ℂ))
  let G : ℝ × ℝ → ℂ :=
    fun q : ℝ × ℝ =>
      (-1 / (((c : ℂ) + q.2 * Complex.I) - 1)) *
        K q.1 *
        Complex.exp
          (Complex.I * (q.2 : ℂ) * (q.1 : ℂ)) *
        Complex.exp (((c - 1 : ℝ) : ℂ) * (q.1 : ℂ))
  have hF_set :
      IntegrableOn F (Set.Icc (-T) T ×ˢ Set.univ) :=
    fixedRightLine_fourierCauchy_symmetricWindow_productIntegrable
      K hK_cont hK_compact hK_smooth c hc T
  have hF_product :
      Integrable F
        ((volume.restrict (Set.Icc (-T) T)).prod
          (volume.restrict Set.univ)) :=
    Eq.mp
      (congrArg
        (fun μ : MeasureTheory.Measure (ℝ × ℝ) => Integrable F μ)
        (MeasureTheory.Measure.prod_restrict
          (μ := volume) (ν := volume)
          (s := Set.Icc (-T) T) (t := Set.univ)).symm)
      hF_set
  have hG_product :
      Integrable G
        ((volume.restrict Set.univ).prod
          (volume.restrict (Set.Icc (-T) T))) :=
    hF_product.swap
  exact
    Eq.mp
      (congrArg
        (fun μ : MeasureTheory.Measure (ℝ × ℝ) => Integrable G μ)
        (MeasureTheory.Measure.prod_restrict
          (μ := volume) (ν := volume)
          (s := Set.univ) (t := Set.Icc (-T) T)))
      hG_product

/-- Reversed Fubini form of the scalar-window product integral. -/
theorem fixedRightLine_scalarWindow_reversedIterated_eq_swappedProductIntegral
    (K : ℝ → ℂ) (hK_cont : Continuous K) (hK_compact : HasCompactSupport K)
    (hK_smooth : ContDiff ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) K)
    (c : ℝ) (hc : 1 < c) (T : ℝ) :
    (∫ x : ℝ,
        ∫ t in Set.Icc (-T) T,
          (-1 / (((c : ℂ) + t * Complex.I) - 1)) *
            K x *
            Complex.exp
              (Complex.I * (t : ℂ) * (x : ℂ)) *
            Complex.exp (((c - 1 : ℝ) : ℂ) * (x : ℂ))) =
      ∫ q in Set.univ ×ˢ Set.Icc (-T) T,
        (-1 / (((c : ℂ) + q.2 * Complex.I) - 1)) *
          K q.1 *
          Complex.exp
            (Complex.I * (q.2 : ℂ) * (q.1 : ℂ)) *
          Complex.exp (((c - 1 : ℝ) : ℂ) * (q.1 : ℂ)) := by
  exact
    (setIntegral_prod
      (fun q : ℝ × ℝ =>
        (-1 / (((c : ℂ) + q.2 * Complex.I) - 1)) *
          K q.1 *
          Complex.exp
            (Complex.I * (q.2 : ℂ) * (q.1 : ℂ)) *
          Complex.exp (((c - 1 : ℝ) : ℂ) * (q.1 : ℂ)))
      (fixedRightLine_scalarWindow_swappedProductIntegrable
        K hK_cont hK_compact hK_smooth c hc T)).symm

/-- Swapping coordinates sends the reversed product integral to the standard
finite-window product integral. -/
theorem fixedRightLine_scalarWindow_swappedProductIntegral_eq_productIntegral_measureSwap
    (K : ℝ → ℂ) (hK_cont : Continuous K) (hK_compact : HasCompactSupport K)
    (hK_smooth : ContDiff ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) K)
    (c : ℝ) (hc : 1 < c) (T : ℝ) :
    (∫ q,
        ((-1 / (((c : ℂ) + q.2 * Complex.I) - 1)) *
          K q.1 *
          Complex.exp
            (Complex.I * (q.2 : ℂ) * (q.1 : ℂ)) *
          Complex.exp (((c - 1 : ℝ) : ℂ) * (q.1 : ℂ)))
        ∂((volume.restrict Set.univ).prod
          (volume.restrict (Set.Icc (-T) T)))) =
      ∫ p,
        ((-1 / (((c : ℂ) + p.1 * Complex.I) - 1)) *
          K p.2 *
          Complex.exp
            (Complex.I * (p.1 : ℂ) * (p.2 : ℂ)) *
          Complex.exp (((c - 1 : ℝ) : ℂ) * (p.2 : ℂ)))
        ∂((volume.restrict (Set.Icc (-T) T)).prod
          (volume.restrict Set.univ)) := by
  exact
    integral_prod_swap
      (fun p : ℝ × ℝ =>
        (-1 / (((c : ℂ) + p.1 * Complex.I) - 1)) *
          K p.2 *
          Complex.exp
            (Complex.I * (p.1 : ℂ) * (p.2 : ℂ)) *
          Complex.exp (((c - 1 : ℝ) : ℂ) * (p.2 : ℂ)))

/-- Set-integral normalization for the swapped finite-window product integral. -/
theorem fixedRightLine_scalarWindow_swappedProduct_setIntegral_eq_restrictedProductIntegral
    (K : ℝ → ℂ) (hK_cont : Continuous K) (hK_compact : HasCompactSupport K)
    (hK_smooth : ContDiff ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) K)
    (c : ℝ) (hc : 1 < c) (T : ℝ) :
    (∫ q in Set.univ ×ˢ Set.Icc (-T) T,
        (-1 / (((c : ℂ) + q.2 * Complex.I) - 1)) *
          K q.1 *
          Complex.exp
            (Complex.I * (q.2 : ℂ) * (q.1 : ℂ)) *
          Complex.exp (((c - 1 : ℝ) : ℂ) * (q.1 : ℂ))) =
      ∫ q,
        ((-1 / (((c : ℂ) + q.2 * Complex.I) - 1)) *
          K q.1 *
          Complex.exp
            (Complex.I * (q.2 : ℂ) * (q.1 : ℂ)) *
          Complex.exp (((c - 1 : ℝ) : ℂ) * (q.1 : ℂ)))
        ∂((volume.restrict Set.univ).prod
          (volume.restrict (Set.Icc (-T) T))) := by
  exact
    (congrArg
      (fun μ : MeasureTheory.Measure (ℝ × ℝ) =>
        ∫ q,
          ((-1 / (((c : ℂ) + q.2 * Complex.I) - 1)) *
            K q.1 *
            Complex.exp
              (Complex.I * (q.2 : ℂ) * (q.1 : ℂ)) *
            Complex.exp (((c - 1 : ℝ) : ℂ) * (q.1 : ℂ))) ∂μ)
      (MeasureTheory.Measure.prod_restrict
        (μ := volume) (ν := volume)
        (s := Set.univ) (t := Set.Icc (-T) T))).symm

/-- Set-integral normalization for the standard finite-window product integral. -/
theorem fixedRightLine_scalarWindow_product_setIntegral_eq_restrictedProductIntegral
    (K : ℝ → ℂ) (hK_cont : Continuous K) (hK_compact : HasCompactSupport K)
    (hK_smooth : ContDiff ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) K)
    (c : ℝ) (hc : 1 < c) (T : ℝ) :
    (∫ p in Set.Icc (-T) T ×ˢ Set.univ,
        (-1 / (((c : ℂ) + p.1 * Complex.I) - 1)) *
          K p.2 *
          Complex.exp
            (Complex.I * (p.1 : ℂ) * (p.2 : ℂ)) *
          Complex.exp (((c - 1 : ℝ) : ℂ) * (p.2 : ℂ))) =
      ∫ p,
        ((-1 / (((c : ℂ) + p.1 * Complex.I) - 1)) *
          K p.2 *
          Complex.exp
            (Complex.I * (p.1 : ℂ) * (p.2 : ℂ)) *
          Complex.exp (((c - 1 : ℝ) : ℂ) * (p.2 : ℂ)))
        ∂((volume.restrict (Set.Icc (-T) T)).prod
          (volume.restrict Set.univ)) := by
  exact
    (congrArg
      (fun μ : MeasureTheory.Measure (ℝ × ℝ) =>
        ∫ p,
          ((-1 / (((c : ℂ) + p.1 * Complex.I) - 1)) *
            K p.2 *
            Complex.exp
              (Complex.I * (p.1 : ℂ) * (p.2 : ℂ)) *
            Complex.exp (((c - 1 : ℝ) : ℂ) * (p.2 : ℂ))) ∂μ)
      (MeasureTheory.Measure.prod_restrict
        (μ := volume) (ν := volume)
        (s := Set.Icc (-T) T) (t := Set.univ))).symm

/-- Swapping coordinates sends the reversed product integral to the standard
finite-window product integral. -/
theorem fixedRightLine_scalarWindow_swappedProductIntegral_eq_productIntegral
    (K : ℝ → ℂ) (hK_cont : Continuous K) (hK_compact : HasCompactSupport K)
    (hK_smooth : ContDiff ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) K)
    (c : ℝ) (hc : 1 < c) (T : ℝ) :
    (∫ q in Set.univ ×ˢ Set.Icc (-T) T,
        (-1 / (((c : ℂ) + q.2 * Complex.I) - 1)) *
          K q.1 *
          Complex.exp
            (Complex.I * (q.2 : ℂ) * (q.1 : ℂ)) *
          Complex.exp (((c - 1 : ℝ) : ℂ) * (q.1 : ℂ))) =
      ∫ p in Set.Icc (-T) T ×ˢ Set.univ,
        (-1 / (((c : ℂ) + p.1 * Complex.I) - 1)) *
          K p.2 *
          Complex.exp
            (Complex.I * (p.1 : ℂ) * (p.2 : ℂ)) *
          Complex.exp (((c - 1 : ℝ) : ℂ) * (p.2 : ℂ)) := by
  calc
    (∫ q in Set.univ ×ˢ Set.Icc (-T) T,
        (-1 / (((c : ℂ) + q.2 * Complex.I) - 1)) *
          K q.1 *
          Complex.exp
            (Complex.I * (q.2 : ℂ) * (q.1 : ℂ)) *
          Complex.exp (((c - 1 : ℝ) : ℂ) * (q.1 : ℂ)))
        =
        ∫ q,
          ((-1 / (((c : ℂ) + q.2 * Complex.I) - 1)) *
            K q.1 *
            Complex.exp
              (Complex.I * (q.2 : ℂ) * (q.1 : ℂ)) *
            Complex.exp (((c - 1 : ℝ) : ℂ) * (q.1 : ℂ)))
          ∂((volume.restrict Set.univ).prod
            (volume.restrict (Set.Icc (-T) T))) := by
          exact
            fixedRightLine_scalarWindow_swappedProduct_setIntegral_eq_restrictedProductIntegral
              K hK_cont hK_compact hK_smooth c hc T
    _ =
        ∫ p,
          ((-1 / (((c : ℂ) + p.1 * Complex.I) - 1)) *
            K p.2 *
            Complex.exp
              (Complex.I * (p.1 : ℂ) * (p.2 : ℂ)) *
            Complex.exp (((c - 1 : ℝ) : ℂ) * (p.2 : ℂ)))
          ∂((volume.restrict (Set.Icc (-T) T)).prod
            (volume.restrict Set.univ)) := by
          exact
            fixedRightLine_scalarWindow_swappedProductIntegral_eq_productIntegral_measureSwap
              K hK_cont hK_compact hK_smooth c hc T
    _ =
        ∫ p in Set.Icc (-T) T ×ˢ Set.univ,
          (-1 / (((c : ℂ) + p.1 * Complex.I) - 1)) *
            K p.2 *
            Complex.exp
              (Complex.I * (p.1 : ℂ) * (p.2 : ℂ)) *
            Complex.exp (((c - 1 : ℝ) : ℂ) * (p.2 : ℂ)) := by
          exact
            (fixedRightLine_scalarWindow_product_setIntegral_eq_restrictedProductIntegral
              K hK_cont hK_compact hK_smooth c hc T).symm

/-- Reversed Fubini form of the scalar-window product integral. -/
theorem fixedRightLine_scalarWindow_reversedIterated_eq_productIntegral
    (K : ℝ → ℂ) (hK_cont : Continuous K) (hK_compact : HasCompactSupport K)
    (hK_smooth : ContDiff ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) K)
    (c : ℝ) (hc : 1 < c) (T : ℝ) :
    (∫ x : ℝ,
        ∫ t in Set.Icc (-T) T,
          (-1 / (((c : ℂ) + t * Complex.I) - 1)) *
            K x *
            Complex.exp
              (Complex.I * (t : ℂ) * (x : ℂ)) *
            Complex.exp (((c - 1 : ℝ) : ℂ) * (x : ℂ))) =
      ∫ p in Set.Icc (-T) T ×ˢ Set.univ,
        (-1 / (((c : ℂ) + p.1 * Complex.I) - 1)) *
          K p.2 *
          Complex.exp
            (Complex.I * (p.1 : ℂ) * (p.2 : ℂ)) *
          Complex.exp (((c - 1 : ℝ) : ℂ) * (p.2 : ℂ)) := by
  calc
    (∫ x : ℝ,
        ∫ t in Set.Icc (-T) T,
          (-1 / (((c : ℂ) + t * Complex.I) - 1)) *
            K x *
            Complex.exp
              (Complex.I * (t : ℂ) * (x : ℂ)) *
            Complex.exp (((c - 1 : ℝ) : ℂ) * (x : ℂ)))
        =
        ∫ q in Set.univ ×ˢ Set.Icc (-T) T,
          (-1 / (((c : ℂ) + q.2 * Complex.I) - 1)) *
            K q.1 *
            Complex.exp
              (Complex.I * (q.2 : ℂ) * (q.1 : ℂ)) *
            Complex.exp (((c - 1 : ℝ) : ℂ) * (q.1 : ℂ)) := by
          exact
            fixedRightLine_scalarWindow_reversedIterated_eq_swappedProductIntegral
              K hK_cont hK_compact hK_smooth c hc T
    _ =
        ∫ p in Set.Icc (-T) T ×ˢ Set.univ,
          (-1 / (((c : ℂ) + p.1 * Complex.I) - 1)) *
            K p.2 *
            Complex.exp
              (Complex.I * (p.1 : ℂ) * (p.2 : ℂ)) *
            Complex.exp (((c - 1 : ℝ) : ℂ) * (p.2 : ℂ)) := by
          exact
            fixedRightLine_scalarWindow_swappedProductIntegral_eq_productIntegral
              K hK_cont hK_compact hK_smooth c hc T

/-- The scalar-window integral is the same finite-window product integral. -/
theorem fixedRightLine_scalarWindowIntegral_eq_productIntegral
    (K : ℝ → ℂ) (hK_cont : Continuous K) (hK_compact : HasCompactSupport K)
    (hK_smooth : ContDiff ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) K)
    (c : ℝ) (hc : 1 < c) (T : ℝ) :
    (∫ x : ℝ,
        K x *
          (∫ t in Set.Icc (-T) T,
            (-1 / (((c : ℂ) + t * Complex.I) - 1)) *
              Complex.exp
                (Complex.I * (t : ℂ) * (x : ℂ)) *
              Complex.exp (((c - 1 : ℝ) : ℂ) * (x : ℂ)))) =
      ∫ p in Set.Icc (-T) T ×ˢ Set.univ,
        (-1 / (((c : ℂ) + p.1 * Complex.I) - 1)) *
          K p.2 *
          Complex.exp
            (Complex.I * (p.1 : ℂ) * (p.2 : ℂ)) *
          Complex.exp (((c - 1 : ℝ) : ℂ) * (p.2 : ℂ)) := by
  calc
    (∫ x : ℝ,
        K x *
          (∫ t in Set.Icc (-T) T,
            (-1 / (((c : ℂ) + t * Complex.I) - 1)) *
              Complex.exp
                (Complex.I * (t : ℂ) * (x : ℂ)) *
              Complex.exp (((c - 1 : ℝ) : ℂ) * (x : ℂ)))
        =
        ∫ x : ℝ,
          ∫ t in Set.Icc (-T) T,
            (-1 / (((c : ℂ) + t * Complex.I) - 1)) *
              K x *
              Complex.exp
                (Complex.I * (t : ℂ) * (x : ℂ)) *
              Complex.exp (((c - 1 : ℝ) : ℂ) * (x : ℂ)) := by
          exact
            fixedRightLine_scalarWindowIntegral_eq_reversedIterated
              K hK_cont hK_compact hK_smooth c hc T
    _ =
        ∫ p in Set.Icc (-T) T ×ˢ Set.univ,
          (-1 / (((c : ℂ) + p.1 * Complex.I) - 1)) *
            K p.2 *
            Complex.exp
              (Complex.I * (p.1 : ℂ) * (p.2 : ℂ)) *
            Complex.exp (((c - 1 : ℝ) : ℂ) * (p.2 : ℂ)) := by
          exact
            fixedRightLine_scalarWindow_reversedIterated_eq_productIntegral
              K hK_cont hK_compact hK_smooth c hc T

/-- Finite-window Fubini form of the fixed-right-line Cauchy kernel. -/
theorem fixedRightLine_fourierCauchy_symmetricWindow_eq_scalarWindowIntegral
    (K : ℝ → ℂ) (hK_cont : Continuous K) (hK_compact : HasCompactSupport K)
    (hK_smooth : ContDiff ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) K)
    (c : ℝ) (hc : 1 < c) (T : ℝ) :
    (∫ t in Set.Icc (-T) T,
        (-1 / (((c : ℂ) + t * Complex.I) - 1)) *
          (∫ x : ℝ,
            K x *
              Complex.exp
                (Complex.I * (t : ℂ) * (x : ℂ)) *
              Complex.exp (((c - 1 : ℝ) : ℂ) * (x : ℂ)))) =
      ∫ x : ℝ,
        K x *
          (∫ t in Set.Icc (-T) T,
            (-1 / (((c : ℂ) + t * Complex.I) - 1)) *
              Complex.exp
                (Complex.I * (t : ℂ) * (x : ℂ)) *
              Complex.exp (((c - 1 : ℝ) : ℂ) * (x : ℂ))) := by
  calc
    (∫ t in Set.Icc (-T) T,
        (-1 / (((c : ℂ) + t * Complex.I) - 1)) *
          (∫ x : ℝ,
            K x *
              Complex.exp
                (Complex.I * (t : ℂ) * (x : ℂ)) *
              Complex.exp (((c - 1 : ℝ) : ℂ) * (x : ℂ))))
        =
        ∫ p in Set.Icc (-T) T ×ˢ Set.univ,
          (-1 / (((c : ℂ) + p.1 * Complex.I) - 1)) *
            K p.2 *
            Complex.exp
              (Complex.I * (p.1 : ℂ) * (p.2 : ℂ)) *
            Complex.exp (((c - 1 : ℝ) : ℂ) * (p.2 : ℂ)) := by
          exact
            fixedRightLine_fourierCauchy_symmetricWindow_eq_productIntegral
              K hK_cont hK_compact hK_smooth c hc T
    _ =
        ∫ x : ℝ,
          K x *
            (∫ t in Set.Icc (-T) T,
              (-1 / (((c : ℂ) + t * Complex.I) - 1)) *
                Complex.exp
                  (Complex.I * (t : ℂ) * (x : ℂ)) *
                Complex.exp (((c - 1 : ℝ) : ℂ) * (x : ℂ))) := by
          exact
            (fixedRightLine_scalarWindowIntegral_eq_productIntegral
              K hK_cont hK_compact hK_smooth c hc T).symm

/-- The one-sided scalar projection is unchanged if the endpoint is removed,
because the endpoint has zero Lebesgue mass. -/
theorem fixedRightLine_scalarProjection_Ioi_integral_eq_Ici_integral
    (K : ℝ → ℂ) :
    (∫ x in Set.Ioi (0 : ℝ),
        (-2 * (Real.pi : ℂ)) * K x) =
      ∫ x in Set.Ici (0 : ℝ),
        (-2 * (Real.pi : ℂ)) * K x := by
  exact (integral_Ici_eq_integral_Ioi : _).symm

/-- Positive-time residue value for the normalized Fourier-Laplace denominator.

This is the scalar contour-residue calculation before truncation limits are
transported back to symmetric real-line windows. -/
theorem scalarFourierLaplacePlemelj_positive_residue_value
    (a : ℝ) (ha : 0 < a) (x : ℝ) (hx : x ∈ Set.Ioi (0 : ℝ)) :
    (-2 * (Real.pi : ℂ)) *
        Complex.exp (-(a : ℂ) * (x : ℂ)) =
      (-2 * (Real.pi : ℂ)) *
        Complex.exp (-(a : ℂ) * (x : ℂ)) := by
  exact rfl

/-- Upper semicircle correction term for the positive-time scalar
Fourier-Laplace contour.  The real segment runs from `-T` to `T`, and this arc
returns from `T` to `-T` through the upper half-plane. -/
noncomputable def scalarFourierLaplacePlemelj_positiveUpperArc
    (a x T : ℝ) : ℂ :=
  ∫ θ in (0 : ℝ)..Real.pi,
    let z : ℂ := (T : ℂ) * Complex.exp (Complex.I * (θ : ℂ))
    (-1 / ((a : ℂ) + z * Complex.I)) *
      Complex.exp (Complex.I * z * (x : ℂ)) *
      (Complex.I * (T : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))

/-- Integrand of the positive upper semicircle correction. -/
noncomputable def scalarFourierLaplacePlemelj_positiveUpperArcIntegrand
    (a x T θ : ℝ) : ℂ :=
  let z : ℂ := (T : ℂ) * Complex.exp (Complex.I * (θ : ℂ))
  (-1 / ((a : ℂ) + z * Complex.I)) *
    Complex.exp (Complex.I * z * (x : ℂ)) *
    (Complex.I * (T : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))

/-- The positive upper arc is the interval integral of its named integrand. -/
theorem scalarFourierLaplacePlemelj_positiveUpperArc_eq_integral_integrand
    (a x T : ℝ) :
    scalarFourierLaplacePlemelj_positiveUpperArc a x T =
      ∫ θ in (0 : ℝ)..Real.pi,
        scalarFourierLaplacePlemelj_positiveUpperArcIntegrand a x T θ := by
  rfl

/-- Real Jordan density for the positive upper semicircle estimate. -/
noncomputable def scalarFourierLaplacePlemelj_positiveUpperArcJordanDensity
    (a x T θ : ℝ) : ℝ :=
  (T / (T - a)) * Real.exp (-(T * x * Real.sin θ))

/-- Closed upper-half-plane scalar contour integral for the positive-time
Fourier-Laplace denominator. -/
noncomputable def scalarFourierLaplacePlemelj_positiveClosedContour
    (a x T : ℝ) : ℂ :=
  (∫ t in Set.Icc (-T) T,
    (-1 / ((a : ℂ) + t * Complex.I)) *
      Complex.exp
        (Complex.I * (t : ℂ) * (x : ℂ))) +
    scalarFourierLaplacePlemelj_positiveUpperArc a x T

/-- The positive closed contour unfolds to its real segment plus upper arc. -/
theorem scalarFourierLaplacePlemelj_positiveClosedContour_eq_window_add_upperArc
    (a x T : ℝ) :
    scalarFourierLaplacePlemelj_positiveClosedContour a x T =
      (∫ t in Set.Icc (-T) T,
        (-1 / ((a : ℂ) + t * Complex.I)) *
          Complex.exp
            (Complex.I * (t : ℂ) * (x : ℂ))) +
          scalarFourierLaplacePlemelj_positiveUpperArc a x T := by
  rfl

/-- The pole of the scalar Fourier-Laplace denominator in the upper half-plane. -/
noncomputable def scalarFourierLaplacePlemelj_upperPole
    (a : ℝ) : ℂ :=
  (a : ℂ) * Complex.I

/-- The scalar upper pole lies on the positive imaginary axis. -/
theorem scalarFourierLaplacePlemelj_upperPole_eq
    (a : ℝ) :
    scalarFourierLaplacePlemelj_upperPole a = (a : ℂ) * Complex.I := by
  rfl

/-- The upper pole is inside the positive semicircle once the radius exceeds `a`. -/
theorem scalarFourierLaplacePlemelj_upperPole_mem_upperSemicircleInterior_of_radius
    (a : ℝ) (ha : 0 < a) (T : ℝ) (hT : a < T) :
    ‖scalarFourierLaplacePlemelj_upperPole a‖ < T := by
  have hpole_norm :
      ‖scalarFourierLaplacePlemelj_upperPole a‖ = a := by
    calc
      ‖scalarFourierLaplacePlemelj_upperPole a‖ =
          ‖(a : ℂ) * Complex.I‖ := by
        exact congrArg norm
          (scalarFourierLaplacePlemelj_upperPole_eq a)
      _ = ‖(a : ℂ)‖ * ‖Complex.I‖ := by
        exact norm_mul (a : ℂ) Complex.I
      _ = |a| * ‖Complex.I‖ := by
        exact congrArg
          (fun r : ℝ => r * ‖Complex.I‖)
          (RCLike.norm_ofReal (K := ℂ) a)
      _ = a * ‖Complex.I‖ := by
        exact congrArg
          (fun r : ℝ => r * ‖Complex.I‖)
          (abs_of_pos ha)
      _ = a * 1 := by
        exact congrArg
          (fun r : ℝ => a * r)
          Complex.norm_I
      _ = a := by
        exact mul_one a
  exact hpole_norm.trans_lt hT

/-- Residue of the positive-time normalized scalar kernel at the upper pole. -/
noncomputable def scalarFourierLaplacePlemelj_positiveUpperPoleResidueContribution
    (a x : ℝ) : ℂ :=
  (-2 * (Real.pi : ℂ)) *
    Complex.exp (-(a : ℂ) * (x : ℂ))

/-- Evaluation of the positive-time normalized scalar residue at the upper pole. -/
theorem scalarFourierLaplacePlemelj_positiveUpperPoleResidueContribution_eq
    (a : ℝ) (ha : 0 < a) (x : ℝ) (hx : x ∈ Set.Ioi (0 : ℝ)) :
    scalarFourierLaplacePlemelj_positiveUpperPoleResidueContribution a x =
      (-2 * (Real.pi : ℂ)) *
        Complex.exp (-(a : ℂ) * (x : ℂ)) := by
  exact rfl

/-- Owner residue theorem for the positive-time upper semicircle contour. -/
theorem scalarFourierLaplacePlemelj_positiveClosedContour_eq_residueValue_owner
    (a : ℝ) (ha : 0 < a) (x : ℝ) (hx : x ∈ Set.Ioi (0 : ℝ))
    (T : ℝ)
    (_hpole : ‖scalarFourierLaplacePlemelj_upperPole a‖ < T) :
    scalarFourierLaplacePlemelj_positiveClosedContour a x T =
      (-2 * (Real.pi : ℂ)) *
        Complex.exp (-(a : ℂ) * (x : ℂ)) := by
  sorry

/-- Upper semicircle contour integral equals the abstract upper-pole residue contribution. -/
theorem scalarFourierLaplacePlemelj_positiveClosedContour_eq_upperPoleResidueContribution
    (a : ℝ) (ha : 0 < a) (x : ℝ) (hx : x ∈ Set.Ioi (0 : ℝ))
    (T : ℝ)
    (_hpole : ‖scalarFourierLaplacePlemelj_upperPole a‖ < T) :
    scalarFourierLaplacePlemelj_positiveClosedContour a x T =
      scalarFourierLaplacePlemelj_positiveUpperPoleResidueContribution a x := by
  exact
    (scalarFourierLaplacePlemelj_positiveClosedContour_eq_residueValue_owner
      a ha x hx T _hpole).trans
      (scalarFourierLaplacePlemelj_positiveUpperPoleResidueContribution_eq
        a ha x hx).symm

/-- Upper semicircle contour integral equals the residue contribution once the pole
is inside the contour. -/
theorem scalarFourierLaplacePlemelj_positiveClosedContour_eq_residue_of_upperPoleInside
    (a : ℝ) (ha : 0 < a) (x : ℝ) (hx : x ∈ Set.Ioi (0 : ℝ))
    (T : ℝ)
    (_hpole : ‖scalarFourierLaplacePlemelj_upperPole a‖ < T) :
    scalarFourierLaplacePlemelj_positiveClosedContour a x T =
      (-2 * (Real.pi : ℂ)) *
        Complex.exp (-(a : ℂ) * (x : ℂ)) := by
  exact
    (scalarFourierLaplacePlemelj_positiveClosedContour_eq_upperPoleResidueContribution
      a ha x hx T _hpole).trans
      (scalarFourierLaplacePlemelj_positiveUpperPoleResidueContribution_eq
        a ha x hx)

/-- Radius-qualified upper-half-plane residue theorem for the positive-time scalar
closed contour. -/
theorem scalarFourierLaplacePlemelj_positiveClosedContour_eq_residueValue_of_poleInside
    (a : ℝ) (ha : 0 < a) (x : ℝ) (hx : x ∈ Set.Ioi (0 : ℝ))
    (T : ℝ) (hT : a < T) :
    scalarFourierLaplacePlemelj_positiveClosedContour a x T =
      (-2 * (Real.pi : ℂ)) *
        Complex.exp (-(a : ℂ) * (x : ℂ)) := by
  exact
    scalarFourierLaplacePlemelj_positiveClosedContour_eq_residue_of_upperPoleInside
      a ha x hx T
      (scalarFourierLaplacePlemelj_upperPole_mem_upperSemicircleInterior_of_radius
        a ha T hT)

/-- Upper-half-plane residue theorem for the positive-time scalar closed contour. -/
theorem scalarFourierLaplacePlemelj_positiveClosedContour_eq_residueValue_residueTheorem
    (a : ℝ) (ha : 0 < a) (x : ℝ) (hx : x ∈ Set.Ioi (0 : ℝ)) :
    ∀ᶠ T in atTop,
      scalarFourierLaplacePlemelj_positiveClosedContour a x T =
        (-2 * (Real.pi : ℂ)) *
          Complex.exp (-(a : ℂ) * (x : ℂ)) := by
  exact (eventually_gt_atTop a).mono
    (fun T hT =>
      scalarFourierLaplacePlemelj_positiveClosedContour_eq_residueValue_of_poleInside
        a ha x hx T hT)

/-- Finite upper-half-plane residue identity for the positive-time scalar
Fourier-Laplace contour. -/
theorem scalarFourierLaplacePlemelj_positive_window_add_upperArc_eq_residueValue
    (a : ℝ) (ha : 0 < a) (x : ℝ) (hx : x ∈ Set.Ioi (0 : ℝ)) :
    ∀ᶠ T in atTop,
      (∫ t in Set.Icc (-T) T,
        (-1 / ((a : ℂ) + t * Complex.I)) *
          Complex.exp
            (Complex.I * (t : ℂ) * (x : ℂ))) +
          scalarFourierLaplacePlemelj_positiveUpperArc a x T =
        (-2 * (Real.pi : ℂ)) *
          Complex.exp (-(a : ℂ) * (x : ℂ)) := by
  have hclosed :
      ∀ᶠ T in atTop,
        scalarFourierLaplacePlemelj_positiveClosedContour a x T =
          (-2 * (Real.pi : ℂ)) *
            Complex.exp (-(a : ℂ) * (x : ℂ)) :=
    scalarFourierLaplacePlemelj_positiveClosedContour_eq_residueValue_residueTheorem
      a ha x hx
  exact hclosed.mono
    (fun T hT =>
      (scalarFourierLaplacePlemelj_positiveClosedContour_eq_window_add_upperArc
        a x T).symm.trans hT)

/-- Positive upper-arc Jordan majorant. -/
noncomputable def scalarFourierLaplacePlemelj_positiveUpperArcJordanMajorant
    (a x T : ℝ) : ℝ :=
  (Real.pi * T / (T - a)) * ((T * x)⁻¹)

/-- The shifted Jordan denominator tends to infinity with the radius. -/
theorem scalarFourierLaplacePlemelj_jordanShiftedDenominator_tendsto_atTop
    (a : ℝ) :
    Tendsto
      (fun T : ℝ => T - a)
      atTop
      atTop :=
  tendsto_atTop_add_const_right (-a) tendsto_id

/-- The Jordan prefactor remainder tends to zero. -/
theorem scalarFourierLaplacePlemelj_jordanPrefactorRemainder_tendsto_zero
    (a : ℝ) :
    Tendsto
      (fun T : ℝ => Real.pi * a / (T - a))
      atTop
      (𝓝 0) :=
  tendsto_const_nhds.div_atTop
    (scalarFourierLaplacePlemelj_jordanShiftedDenominator_tendsto_atTop a)

/-- Pointwise algebra splitting of the Jordan prefactor away from its shifted
denominator pole. -/
theorem scalarFourierLaplacePlemelj_jordanPrefactor_eq_pi_add_remainder_of_ne
    (a T : ℝ) (hT : T ≠ a) :
    Real.pi * T / (T - a) =
      Real.pi + Real.pi * a / (T - a) := by
  have hden : T - a ≠ 0 :=
    sub_ne_zero.mpr hT
  calc
    Real.pi * T / (T - a) =
        Real.pi * ((T - a) + a) / (T - a) := by
      exact congrArg
        (fun y : ℝ => Real.pi * y / (T - a))
        (sub_add_cancel T a).symm
    _ = (Real.pi * (T - a) + Real.pi * a) / (T - a) := by
      exact congrArg
        (fun y : ℝ => y / (T - a))
        (mul_add Real.pi (T - a) a)
    _ =
        Real.pi * (T - a) / (T - a) +
          Real.pi * a / (T - a) := by
      exact add_div (Real.pi * (T - a)) (Real.pi * a) (T - a)
    _ =
        Real.pi * ((T - a) / (T - a)) +
          Real.pi * a / (T - a) := by
      exact congrArg
        (fun y : ℝ => y + Real.pi * a / (T - a))
        (mul_div_assoc Real.pi (T - a) (T - a))
    _ = Real.pi * 1 + Real.pi * a / (T - a) := by
      exact congrArg
        (fun y : ℝ => Real.pi * y + Real.pi * a / (T - a))
        (div_self hden)
    _ = Real.pi + Real.pi * a / (T - a) := by
      exact congrArg
        (fun y : ℝ => y + Real.pi * a / (T - a))
        (mul_one Real.pi)

/-- Eventually, the Jordan prefactor splits into its limit plus a vanishing
remainder. -/
theorem scalarFourierLaplacePlemelj_jordanPrefactor_eventually_eq_pi_add_remainder
    (a : ℝ) :
    (fun T : ℝ => Real.pi * T / (T - a)) =ᶠ[atTop]
      (fun T : ℝ => Real.pi + Real.pi * a / (T - a)) := by
  exact
    (eventually_ne_atTop a).mono
      (fun T hT =>
        scalarFourierLaplacePlemelj_jordanPrefactor_eq_pi_add_remainder_of_ne
          a T hT)

/-- The positive upper-arc Jordan prefactor has a finite limit. -/
theorem scalarFourierLaplacePlemelj_positiveUpperArcJordanPrefactor_tendsto_pi
    (a : ℝ) :
    Tendsto
      (fun T : ℝ => Real.pi * T / (T - a))
      atTop
      (𝓝 Real.pi) := by
  exact
    Tendsto.congr'
      (scalarFourierLaplacePlemelj_jordanPrefactor_eventually_eq_pi_add_remainder
        a).symm
      (tendsto_const_nhds.add
        (scalarFourierLaplacePlemelj_jordanPrefactorRemainder_tendsto_zero
          a))

/-- The positive upper-arc reciprocal linear factor tends to zero. -/
theorem scalarFourierLaplacePlemelj_positiveUpperArcJordanReciprocal_tendsto_zero
    (x : ℝ) (hx : x ∈ Set.Ioi (0 : ℝ)) :
    Tendsto
      (fun T : ℝ => (T * x)⁻¹)
      atTop
      (𝓝 0) := by
  exact
    tendsto_inv_atTop_zero.comp
      (Tendsto.atTop_mul_const
        (Set.mem_Ioi.mp hx)
        tendsto_id)

/-- The positive upper-arc Jordan majorant tends to zero. -/
theorem scalarFourierLaplacePlemelj_positiveUpperArcJordanMajorant_tendsto_zero
    (a : ℝ) (ha : 0 < a) (x : ℝ) (hx : x ∈ Set.Ioi (0 : ℝ)) :
    Tendsto
      (fun T : ℝ =>
        scalarFourierLaplacePlemelj_positiveUpperArcJordanMajorant a x T)
      atTop
      (𝓝 0) := by
  exact
    (scalarFourierLaplacePlemelj_positiveUpperArcJordanPrefactor_tendsto_pi
      a).mul
      (scalarFourierLaplacePlemelj_positiveUpperArcJordanReciprocal_tendsto_zero
        x hx)

/-- The circular velocity on a positive-radius semicircle has norm equal to the
radius. -/
theorem scalarFourierLaplacePlemelj_semicircleVelocity_norm_eq_radius
    (T : ℝ) (hT : 0 < T) (θ : ℝ) :
    ‖Complex.I * (T : ℂ) * Complex.exp (Complex.I * (θ : ℂ))‖ = T := by
  have hexp_arg :
      Complex.I * (θ : ℂ) = (θ : ℂ) * Complex.I :=
    mul_comm Complex.I (θ : ℂ)
  have hexp_norm :
      ‖Complex.exp (Complex.I * (θ : ℂ))‖ = 1 := by
    exact
      (congrArg
        (fun z : ℂ => ‖Complex.exp z‖)
        hexp_arg).trans
        (Complex.norm_exp_ofReal_mul_I θ)
  have hTnorm :
      ‖(T : ℂ)‖ = T := by
    exact (RCLike.norm_ofReal (K := ℂ) T).trans
      (abs_of_pos hT)
  calc
    ‖Complex.I * (T : ℂ) * Complex.exp (Complex.I * (θ : ℂ))‖ =
        ‖Complex.I * (T : ℂ)‖ *
          ‖Complex.exp (Complex.I * (θ : ℂ))‖ := by
      exact norm_mul (Complex.I * (T : ℂ))
        (Complex.exp (Complex.I * (θ : ℂ)))
    _ =
        (‖Complex.I‖ * ‖(T : ℂ)‖) *
          ‖Complex.exp (Complex.I * (θ : ℂ))‖ := by
      exact congrArg
        (fun r : ℝ => r * ‖Complex.exp (Complex.I * (θ : ℂ))‖)
        (norm_mul Complex.I (T : ℂ))
    _ = (1 * ‖(T : ℂ)‖) *
          ‖Complex.exp (Complex.I * (θ : ℂ))‖ := by
      exact congrArg
        (fun r : ℝ => (r * ‖(T : ℂ)‖) *
          ‖Complex.exp (Complex.I * (θ : ℂ))‖)
        Complex.norm_I
    _ = ‖(T : ℂ)‖ *
          ‖Complex.exp (Complex.I * (θ : ℂ))‖ := by
      exact congrArg
        (fun r : ℝ => r * ‖Complex.exp (Complex.I * (θ : ℂ))‖)
        (one_mul ‖(T : ℂ)‖)
    _ = T * ‖Complex.exp (Complex.I * (θ : ℂ))‖ := by
      exact congrArg
        (fun r : ℝ => r * ‖Complex.exp (Complex.I * (θ : ℂ))‖)
        hTnorm
    _ = T * 1 := by
      exact congrArg
        (fun r : ℝ => T * r)
        hexp_norm
    _ = T := by
      exact mul_one T

/-- Real coordinate of the scalar semicircle point. -/
theorem scalarFourierLaplacePlemelj_semicirclePoint_re
    (T θ : ℝ) :
    ((T : ℂ) * Complex.exp (Complex.I * (θ : ℂ))).re =
      T * Real.cos θ := by
  have harg :
      Complex.I * (θ : ℂ) = (θ : ℂ) * Complex.I :=
    mul_comm Complex.I (θ : ℂ)
  have hexp_im :
      (Complex.exp (Complex.I * (θ : ℂ))).im = Real.sin θ :=
    (congrArg
      (fun z : ℂ => (Complex.exp z).im)
      harg).trans
      (Complex.exp_ofReal_mul_I_im θ)
  calc
    ((T : ℂ) * Complex.exp (Complex.I * (θ : ℂ))).re =
        (T : ℂ).re * (Complex.exp (Complex.I * (θ : ℂ))).re -
          (T : ℂ).im * (Complex.exp (Complex.I * (θ : ℂ))).im := by
      exact Complex.mul_re (T : ℂ)
        (Complex.exp (Complex.I * (θ : ℂ)))
    _ =
        T * (Complex.exp (Complex.I * (θ : ℂ))).re -
          (T : ℂ).im * (Complex.exp (Complex.I * (θ : ℂ))).im := by
      exact congrArg
        (fun r : ℝ =>
          r * (Complex.exp (Complex.I * (θ : ℂ))).re -
            (T : ℂ).im * (Complex.exp (Complex.I * (θ : ℂ))).im)
        (Complex.ofReal_re T)
    _ =
        T * (Complex.exp (Complex.I * (θ : ℂ))).re -
          0 * (Complex.exp (Complex.I * (θ : ℂ))).im := by
      exact congrArg
        (fun r : ℝ =>
          T * (Complex.exp (Complex.I * (θ : ℂ))).re -
            r * (Complex.exp (Complex.I * (θ : ℂ))).im)
        (Complex.ofReal_im T)
    _ =
        T * (Complex.exp (Complex.I * (θ : ℂ))).re - 0 := by
      exact congrArg
        (fun r : ℝ =>
          T * (Complex.exp (Complex.I * (θ : ℂ))).re - r)
        (zero_mul (Complex.exp (Complex.I * (θ : ℂ))).im)
    _ = T * (Complex.exp (Complex.I * (θ : ℂ))).re := by
      exact sub_zero (T * (Complex.exp (Complex.I * (θ : ℂ))).re)
    _ = T * Real.cos θ := by
      exact congrArg
        (fun r : ℝ => T * r)
        hexp_re

/-- Imaginary coordinate of the scalar semicircle point. -/
theorem scalarFourierLaplacePlemelj_semicirclePoint_im
    (T θ : ℝ) :
    ((T : ℂ) * Complex.exp (Complex.I * (θ : ℂ))).im =
      T * Real.sin θ := by
  have harg :
      Complex.I * (θ : ℂ) = (θ : ℂ) * Complex.I :=
    mul_comm Complex.I (θ : ℂ)
  have hexp_re :
      (Complex.exp (Complex.I * (θ : ℂ))).re = Real.cos θ :=
    (congrArg
      (fun z : ℂ => (Complex.exp z).re)
      harg).trans
      (Complex.exp_ofReal_mul_I_re θ)
  have hexp_im :
      (Complex.exp (Complex.I * (θ : ℂ))).im = Real.sin θ :=
    (congrArg
      (fun z : ℂ => (Complex.exp z).im)
      harg).trans
      (Complex.exp_ofReal_mul_I_im θ)
  calc
    ((T : ℂ) * Complex.exp (Complex.I * (θ : ℂ))).im =
        (T : ℂ).re * (Complex.exp (Complex.I * (θ : ℂ))).im +
          (T : ℂ).im * (Complex.exp (Complex.I * (θ : ℂ))).re := by
      exact Complex.mul_im (T : ℂ)
        (Complex.exp (Complex.I * (θ : ℂ)))
    _ =
        T * (Complex.exp (Complex.I * (θ : ℂ))).im +
          (T : ℂ).im * (Complex.exp (Complex.I * (θ : ℂ))).re := by
      exact congrArg
        (fun r : ℝ =>
          r * (Complex.exp (Complex.I * (θ : ℂ))).im +
            (T : ℂ).im * (Complex.exp (Complex.I * (θ : ℂ))).re)
        (Complex.ofReal_re T)
    _ =
        T * (Complex.exp (Complex.I * (θ : ℂ))).im +
          0 * (Complex.exp (Complex.I * (θ : ℂ))).re := by
      exact congrArg
        (fun r : ℝ =>
          T * (Complex.exp (Complex.I * (θ : ℂ))).im +
            r * (Complex.exp (Complex.I * (θ : ℂ))).re)
        (Complex.ofReal_im T)
    _ =
        T * (Complex.exp (Complex.I * (θ : ℂ))).im + 0 := by
      exact congrArg
        (fun r : ℝ =>
          T * (Complex.exp (Complex.I * (θ : ℂ))).im + r)
        (zero_mul (Complex.exp (Complex.I * (θ : ℂ))).re)
    _ = T * (Complex.exp (Complex.I * (θ : ℂ))).im := by
      exact add_zero (T * (Complex.exp (Complex.I * (θ : ℂ))).im)
    _ = T * Real.sin θ := by
      exact congrArg
        (fun r : ℝ => T * r)
        hexp_im

/-- Real part after multiplication by `Complex.I` on the left. -/
theorem scalarFourierLaplacePlemelj_I_mul_semicirclePoint_re
    (T θ : ℝ) :
    (Complex.I * ((T : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))).re =
      -(T * Real.sin θ) := by
  calc
    (Complex.I * ((T : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))).re =
        -((T : ℂ) * Complex.exp (Complex.I * (θ : ℂ))).im := by
      exact Complex.I_mul_re
        ((T : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))
    _ = -(T * Real.sin θ) := by
      exact congrArg Neg.neg
        (scalarFourierLaplacePlemelj_semicirclePoint_im T θ)

/-- Real scalar rearrangement for the circular exponent damping term. -/
theorem scalarFourierLaplacePlemelj_semicircleExponent_scalar_rearrange
    (x T θ : ℝ) :
    (-(T * Real.sin θ)) * x = -(T * x * Real.sin θ) := by
  have hinner :
      (T * Real.sin θ) * x = T * x * Real.sin θ := by
    calc
      (T * Real.sin θ) * x = T * (Real.sin θ * x) := by
        exact mul_assoc T (Real.sin θ) x
      _ = T * (x * Real.sin θ) := by
        exact congrArg
          (fun r : ℝ => T * r)
          (mul_comm (Real.sin θ) x)
      _ = T * x * Real.sin θ := by
        exact (mul_assoc T x (Real.sin θ)).symm
  calc
    (-(T * Real.sin θ)) * x =
        -((T * Real.sin θ) * x) := by
      exact neg_mul (T * Real.sin θ) x
    _ = -(T * x * Real.sin θ) := by
      exact congrArg Neg.neg hinner

/-- Real part of the scalar Fourier-Laplace exponent on a circular arc. -/
theorem scalarFourierLaplacePlemelj_semicircleExponent_re
    (x T θ : ℝ) :
    (Complex.I *
      ((T : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) *
      (x : ℂ)).re =
      -(T * x * Real.sin θ) := by
  calc
    (Complex.I *
      ((T : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) *
      (x : ℂ)).re =
        (Complex.I *
          ((T : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))).re *
          (x : ℂ).re -
        (Complex.I *
          ((T : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))).im *
          (x : ℂ).im := by
      exact Complex.mul_re
        (Complex.I *
          ((T : ℂ) * Complex.exp (Complex.I * (θ : ℂ))))
        (x : ℂ)
    _ =
        (Complex.I *
          ((T : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))).re *
          x -
        (Complex.I *
          ((T : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))).im *
          (x : ℂ).im := by
      exact congrArg
        (fun r : ℝ =>
          (Complex.I *
            ((T : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))).re *
            r -
          (Complex.I *
            ((T : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))).im *
            (x : ℂ).im)
        (Complex.ofReal_re x)
    _ =
        (Complex.I *
          ((T : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))).re *
          x -
        (Complex.I *
          ((T : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))).im *
          0 := by
      exact congrArg
        (fun r : ℝ =>
          (Complex.I *
            ((T : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))).re *
            x -
          (Complex.I *
            ((T : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))).im *
            r)
        (Complex.ofReal_im x)
    _ =
        (Complex.I *
          ((T : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))).re * x -
        0 := by
      exact congrArg
        (fun r : ℝ =>
          (Complex.I *
            ((T : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))).re * x - r)
        (mul_zero
          (Complex.I *
            ((T : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))).im)
    _ =
        (Complex.I *
          ((T : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))).re * x := by
      exact sub_zero
        ((Complex.I *
          ((T : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))).re * x)
    _ = (-(T * Real.sin θ)) * x := by
      exact congrArg
        (fun r : ℝ => r * x)
        (scalarFourierLaplacePlemelj_I_mul_semicirclePoint_re T θ)
    _ = -(T * x * Real.sin θ) := by
      exact scalarFourierLaplacePlemelj_semicircleExponent_scalar_rearrange
        x T θ

/-- The denominator arc factor has radius norm. -/
theorem scalarFourierLaplacePlemelj_semicirclePoint_mul_I_norm_eq_radius
    (T : ℝ) (hT : 0 < T) (θ : ℝ) :
    ‖((T : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) * Complex.I‖ = T := by
  have harg :
      Complex.I * (θ : ℂ) = (θ : ℂ) * Complex.I :=
    mul_comm Complex.I (θ : ℂ)
  have hexp_norm :
      ‖Complex.exp (Complex.I * (θ : ℂ))‖ = 1 :=
    (congrArg
      (fun z : ℂ => ‖Complex.exp z‖)
      harg).trans
      (Complex.norm_exp_ofReal_mul_I θ)
  have hTnorm :
      ‖(T : ℂ)‖ = T :=
    (RCLike.norm_ofReal (K := ℂ) T).trans
      (abs_of_pos hT)
  calc
    ‖((T : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) * Complex.I‖ =
        ‖(T : ℂ) * Complex.exp (Complex.I * (θ : ℂ))‖ *
          ‖Complex.I‖ := by
      exact norm_mul
        ((T : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))
        Complex.I
    _ =
        (‖(T : ℂ)‖ *
          ‖Complex.exp (Complex.I * (θ : ℂ))‖) *
          ‖Complex.I‖ := by
      exact congrArg
        (fun r : ℝ => r * ‖Complex.I‖)
        (norm_mul (T : ℂ) (Complex.exp (Complex.I * (θ : ℂ))))
    _ =
        (T * ‖Complex.exp (Complex.I * (θ : ℂ))‖) *
          ‖Complex.I‖ := by
      exact congrArg
        (fun r : ℝ =>
          (r * ‖Complex.exp (Complex.I * (θ : ℂ))‖) *
            ‖Complex.I‖)
        hTnorm
    _ = (T * 1) * ‖Complex.I‖ := by
      exact congrArg
        (fun r : ℝ => (T * r) * ‖Complex.I‖)
        hexp_norm
    _ = T * ‖Complex.I‖ := by
      exact congrArg
        (fun r : ℝ => r * ‖Complex.I‖)
        (mul_one T)
    _ = T * 1 := by
      exact congrArg
        (fun r : ℝ => T * r)
        Complex.norm_I
    _ = T := by
      exact mul_one T

/-- Reverse-triangle lower bound for the scalar Cauchy denominator on a
semicircle of radius larger than `a`. -/
theorem scalarFourierLaplacePlemelj_semicircleDenominator_norm_ge_radius_sub
    (a : ℝ) (ha : 0 < a) (T : ℝ) (hT : a < T) (θ : ℝ) :
    T - a ≤
      ‖(a : ℂ) +
        ((T : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) * Complex.I‖ := by
  let zI : ℂ :=
    ((T : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) * Complex.I
  have hTpos : 0 < T :=
    ha.trans hT
  have hzI_norm : ‖zI‖ = T := by
    exact scalarFourierLaplacePlemelj_semicirclePoint_mul_I_norm_eq_radius
      T hTpos θ
  have hneg_norm : ‖(-(a : ℂ))‖ = a := by
    calc
      ‖(-(a : ℂ))‖ = ‖(a : ℂ)‖ := by
        exact norm_neg (a : ℂ)
      _ = |a| := by
        exact RCLike.norm_ofReal (K := ℂ) a
      _ = a := by
        exact abs_of_pos ha
  have hdenom :
      zI - (-(a : ℂ)) =
        (a : ℂ) +
          ((T : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) * Complex.I := by
    calc
      zI - (-(a : ℂ)) = zI + -(-(a : ℂ)) := by
        exact sub_eq_add_neg zI (-(a : ℂ))
      _ = zI + (a : ℂ) := by
        exact congrArg
          (fun w : ℂ => zI + w)
          (neg_neg (a : ℂ))
      _ = (a : ℂ) + zI := by
        exact add_comm zI (a : ℂ)
      _ =
          (a : ℂ) +
            ((T : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) *
              Complex.I := by
        exact rfl
  calc
    T - a = ‖zI‖ - ‖(-(a : ℂ))‖ := by
      exact congrArg₂ HSub.hSub hzI_norm.symm hneg_norm.symm
    _ ≤ ‖zI - (-(a : ℂ))‖ := by
      exact norm_sub_norm_le zI (-(a : ℂ))
    _ =
        ‖(a : ℂ) +
          ((T : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) *
            Complex.I‖ := by
      exact congrArg norm hdenom

/-- Inverse form of the scalar Cauchy denominator lower bound on a semicircle. -/
theorem scalarFourierLaplacePlemelj_semicircleDenominator_inv_norm_le
    (a : ℝ) (ha : 0 < a) (T : ℝ) (hT : a < T) (θ : ℝ) :
    ‖(-1 /
      ((a : ℂ) +
        ((T : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) * Complex.I))‖ ≤
      (T - a)⁻¹ := by
  let den : ℂ :=
    (a : ℂ) +
      ((T : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) * Complex.I
  have hsub_pos : 0 < T - a :=
    sub_pos.mpr hT
  have hden_ge : T - a ≤ ‖den‖ :=
    scalarFourierLaplacePlemelj_semicircleDenominator_norm_ge_radius_sub
      a ha T hT θ
  have hnorm :
      ‖(-1 : ℂ) / den‖ = ‖den‖⁻¹ := by
    calc
      ‖(-1 : ℂ) / den‖ = ‖(-1 : ℂ)‖ / ‖den‖ := by
        exact norm_div (-1 : ℂ) den
      _ = ‖(1 : ℂ)‖ / ‖den‖ := by
        exact congrArg
          (fun r : ℝ => r / ‖den‖)
          (norm_neg (1 : ℂ))
      _ = 1 / ‖den‖ := by
        exact congrArg
          (fun r : ℝ => r / ‖den‖)
          norm_one
      _ = ‖den‖⁻¹ := by
        exact one_div ‖den‖
  exact hnorm.trans_le
    (inv_anti₀ hsub_pos hden_ge)

/-- Algebraic normal form of the Jordan pointwise density. -/
theorem scalarFourierLaplacePlemelj_jordanDensity_eq_inv_mul_exp_mul_radius
    (a T E : ℝ) :
    (T / (T - a)) * E = ((T - a)⁻¹ * E) * T := by
  calc
    (T / (T - a)) * E = (T * (T - a)⁻¹) * E := by
      exact congrArg
        (fun r : ℝ => r * E)
        (div_eq_mul_inv T (T - a))
    _ = T * ((T - a)⁻¹ * E) := by
      exact mul_assoc T (T - a)⁻¹ E
    _ = ((T - a)⁻¹ * E) * T := by
      exact mul_comm T ((T - a)⁻¹ * E)

/-- Algebraic normal form for the Jordan density integral majorant. -/
theorem scalarFourierLaplacePlemelj_jordanPrefactor_mul_pi_inv_eq_majorant
    (a T Y : ℝ) :
    (T / (T - a)) * (Real.pi * Y⁻¹) =
      (Real.pi * T / (T - a)) * Y⁻¹ := by
  calc
    (T / (T - a)) * (Real.pi * Y⁻¹) =
        (T * (T - a)⁻¹) * (Real.pi * Y⁻¹) := by
      exact congrArg
        (fun r : ℝ => r * (Real.pi * Y⁻¹))
        (div_eq_mul_inv T (T - a))
    _ = ((T * (T - a)⁻¹) * Real.pi) * Y⁻¹ := by
      exact mul_assoc (T * (T - a)⁻¹) Real.pi Y⁻¹
    _ = (Real.pi * (T * (T - a)⁻¹)) * Y⁻¹ := by
      exact congrArg
        (fun r : ℝ => r * Y⁻¹)
        (mul_comm (T * (T - a)⁻¹) Real.pi)
    _ = ((Real.pi * T) * (T - a)⁻¹) * Y⁻¹ := by
      exact congrArg
        (fun r : ℝ => r * Y⁻¹)
        (mul_assoc Real.pi T (T - a)⁻¹)
    _ = (Real.pi * T / (T - a)) * Y⁻¹ := by
      exact congrArg
        (fun r : ℝ => r * Y⁻¹)
        (div_eq_mul_inv (Real.pi * T) (T - a)).symm

/-- Denominator part of the positive upper-arc Jordan pointwise estimate. -/
theorem scalarFourierLaplacePlemelj_positiveUpperArc_denominator_norm_inv_le
    (a : ℝ) (ha : 0 < a) (T : ℝ) (hT : a < T) (θ : ℝ) :
    ‖(-1 /
      ((a : ℂ) +
        ((T : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) * Complex.I))‖ ≤
      (T - a)⁻¹ := by
  exact
    scalarFourierLaplacePlemelj_semicircleDenominator_inv_norm_le
      a ha T hT θ

/-- Exponential damping part of the positive upper-arc Jordan pointwise estimate. -/
theorem scalarFourierLaplacePlemelj_positiveUpperArc_exponential_norm_eq_damping
    (x T θ : ℝ) :
    ‖Complex.exp
      (Complex.I *
        ((T : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) *
        (x : ℂ))‖ =
      Real.exp (-(T * x * Real.sin θ)) := by
  calc
    ‖Complex.exp
      (Complex.I *
        ((T : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) *
        (x : ℂ))‖ =
        Complex.abs
          (Complex.exp
            (Complex.I *
              ((T : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) *
              (x : ℂ))) := by
      exact Complex.norm_eq_abs
        (Complex.exp
          (Complex.I *
            ((T : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) *
            (x : ℂ)))
    _ =
        Real.exp
          (Complex.I *
            ((T : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) *
            (x : ℂ)).re := by
      exact Complex.abs_exp
        (Complex.I *
          ((T : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) *
          (x : ℂ))
    _ = Real.exp (-(T * x * Real.sin θ)) := by
      exact congrArg Real.exp
        (scalarFourierLaplacePlemelj_semicircleExponent_re x T θ)

/-- Velocity part of the positive upper-arc Jordan pointwise estimate. -/
theorem scalarFourierLaplacePlemelj_positiveUpperArc_velocity_norm_eq_radius
    (a : ℝ) (ha : 0 < a) (T : ℝ) (hT : a < T) (θ : ℝ) :
    ‖Complex.I * (T : ℂ) * Complex.exp (Complex.I * (θ : ℂ))‖ = T := by
  exact
    scalarFourierLaplacePlemelj_semicircleVelocity_norm_eq_radius
      T (ha.trans hT) θ

/-- Product assembly for the positive upper-arc Jordan pointwise estimate. -/
theorem scalarFourierLaplacePlemelj_positiveUpperArcIntegrand_norm_le_jordanDensity_of_factors
    (a : ℝ) (ha : 0 < a) (x : ℝ) (hx : x ∈ Set.Ioi (0 : ℝ))
    (T : ℝ) (hT : a < T) (θ : ℝ)
    (hden :
      ‖(-1 /
        ((a : ℂ) +
          ((T : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) * Complex.I))‖ ≤
        (T - a)⁻¹)
    (hexp :
      ‖Complex.exp
        (Complex.I *
          ((T : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) *
          (x : ℂ))‖ =
        Real.exp (-(T * x * Real.sin θ)))
    (hvel :
      ‖Complex.I * (T : ℂ) * Complex.exp (Complex.I * (θ : ℂ))‖ = T) :
    ‖scalarFourierLaplacePlemelj_positiveUpperArcIntegrand a x T θ‖ ≤
      scalarFourierLaplacePlemelj_positiveUpperArcJordanDensity a x T θ := by
  let D : ℂ :=
    -1 /
      ((a : ℂ) +
        ((T : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) * Complex.I)
  let E : ℂ :=
    Complex.exp
      (Complex.I *
        ((T : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) *
        (x : ℂ))
  let V : ℂ :=
    Complex.I * (T : ℂ) * Complex.exp (Complex.I * (θ : ℂ))
  let R : ℝ :=
    Real.exp (-(T * x * Real.sin θ))
  have hER : ‖E‖ = R := by
    exact hexp
  have hVR : ‖V‖ = T := by
    exact hvel
  have hV_nonneg : 0 ≤ ‖V‖ :=
    norm_nonneg V
  have hstep :
      (‖D‖ * ‖E‖) * ‖V‖ ≤
        ((T - a)⁻¹ * ‖E‖) * ‖V‖ := by
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hden (norm_nonneg E))
      hV_nonneg
  calc
    ‖scalarFourierLaplacePlemelj_positiveUpperArcIntegrand a x T θ‖ =
        ‖D * E * V‖ := by
      exact rfl
    _ = ‖D * E‖ * ‖V‖ := by
      exact norm_mul (D * E) V
    _ = (‖D‖ * ‖E‖) * ‖V‖ := by
      exact congrArg
        (fun r : ℝ => r * ‖V‖)
        (norm_mul D E)
    _ ≤ ((T - a)⁻¹ * ‖E‖) * ‖V‖ := by
      exact hstep
    _ = ((T - a)⁻¹ * R) * ‖V‖ := by
      exact congrArg
        (fun r : ℝ => ((T - a)⁻¹ * r) * ‖V‖)
        hER
    _ = ((T - a)⁻¹ * R) * T := by
      exact congrArg
        (fun r : ℝ => ((T - a)⁻¹ * R) * r)
        hVR
    _ = (T / (T - a)) * R := by
      exact
        (scalarFourierLaplacePlemelj_jordanDensity_eq_inv_mul_exp_mul_radius
          a T R).symm
    _ = scalarFourierLaplacePlemelj_positiveUpperArcJordanDensity a x T θ := by
      exact rfl

/-- Pointwise Jordan domination of the positive upper-arc integrand. -/
theorem scalarFourierLaplacePlemelj_positiveUpperArcIntegrand_norm_le_jordanDensity
    (a : ℝ) (ha : 0 < a) (x : ℝ) (hx : x ∈ Set.Ioi (0 : ℝ))
    (T : ℝ) (hT : a < T) (θ : ℝ) :
    ‖scalarFourierLaplacePlemelj_positiveUpperArcIntegrand a x T θ‖ ≤
      scalarFourierLaplacePlemelj_positiveUpperArcJordanDensity a x T θ := by
  exact
    scalarFourierLaplacePlemelj_positiveUpperArcIntegrand_norm_le_jordanDensity_of_factors
      a ha x hx T hT θ
      (scalarFourierLaplacePlemelj_positiveUpperArc_denominator_norm_inv_le
        a ha T hT θ)
      (scalarFourierLaplacePlemelj_positiveUpperArc_exponential_norm_eq_damping
        x T θ)
      (scalarFourierLaplacePlemelj_positiveUpperArc_velocity_norm_eq_radius
        a ha T hT θ)

/-- The positive upper-arc Jordan density is interval-integrable. -/
theorem scalarFourierLaplacePlemelj_positiveUpperArcJordanDensity_intervalIntegrable
    (a x T : ℝ) :
    IntervalIntegrable
      (fun θ : ℝ =>
        scalarFourierLaplacePlemelj_positiveUpperArcJordanDensity a x T θ)
      MeasureTheory.volume
      (0 : ℝ)
      Real.pi := by
  have harg :
      Continuous
        (fun θ : ℝ => -(T * x * Real.sin θ)) := by
    exact (continuous_const.mul Real.continuous_sin).neg
  have hexp :
      Continuous
        (fun θ : ℝ => Real.exp (-(T * x * Real.sin θ))) := by
    exact Real.continuous_exp.comp harg
  have hdensity :
      Continuous
        (fun θ : ℝ =>
          scalarFourierLaplacePlemelj_positiveUpperArcJordanDensity a x T θ) := by
    exact continuous_const.mul hexp
  exact hdensity.intervalIntegrable (0 : ℝ) Real.pi

/-- The positive upper-arc Jordan density is nonnegative when the radius is
larger than the pole height. -/
theorem scalarFourierLaplacePlemelj_positiveUpperArcJordanDensity_nonneg
    (a : ℝ) (ha : 0 < a) (x T θ : ℝ) (hT : a < T) :
    0 ≤ scalarFourierLaplacePlemelj_positiveUpperArcJordanDensity a x T θ := by
  have hTpos : 0 < T :=
    ha.trans hT
  have hdenpos : 0 < T - a :=
    sub_pos.mpr hT
  have hpref_nonneg : 0 ≤ T / (T - a) :=
    div_nonneg hTpos.le hdenpos.le
  exact mul_nonneg hpref_nonneg (Real.exp_pos _).le

/-- The positive Jordan density interval integral factors into the constant
prefactor times the scalar sine-damping integral. -/
theorem scalarFourierLaplacePlemelj_positiveUpperArcJordanDensity_integral_eq_prefactor_mul
    (a : ℝ) (T x : ℝ) :
    ∫ θ in (0 : ℝ)..Real.pi,
        scalarFourierLaplacePlemelj_positiveUpperArcJordanDensity a x T θ =
      (T / (T - a)) *
        ∫ θ in (0 : ℝ)..Real.pi,
          Real.exp (-(T * x * Real.sin θ)) := by
  exact intervalIntegral.integral_const_mul
    (T / (T - a))
    (fun θ : ℝ => Real.exp (-(T * x * Real.sin θ)))

/-- The upper sine-damping integrand is interval-integrable on any finite
interval. -/
theorem scalarFourierLaplacePlemelj_upperSineDamping_intervalIntegrable
    (c a b : ℝ) :
    IntervalIntegrable
      (fun θ : ℝ => Real.exp (-(c * Real.sin θ)))
      MeasureTheory.volume
      a
      b := by
  have harg :
      Continuous
        (fun θ : ℝ => -(c * Real.sin θ)) := by
    exact (continuous_const.mul Real.continuous_sin).neg
  have hintegrand :
      Continuous
        (fun θ : ℝ => Real.exp (-(c * Real.sin θ))) := by
    exact Real.continuous_exp.comp harg
  exact hintegrand.intervalIntegrable a b

/-- The upper sine-damping integral splits at `π / 2`. -/
theorem scalarFourierLaplacePlemelj_upperSineDampingIntegral_split_half
    (c : ℝ) :
    ∫ θ in (0 : ℝ)..Real.pi,
        Real.exp (-(c * Real.sin θ)) =
      (∫ θ in (0 : ℝ)..(Real.pi / 2),
        Real.exp (-(c * Real.sin θ))) +
      ∫ θ in (Real.pi / 2)..Real.pi,
        Real.exp (-(c * Real.sin θ)) := by
  have hleft :
      IntervalIntegrable
        (fun θ : ℝ => Real.exp (-(c * Real.sin θ)))
        MeasureTheory.volume
        (0 : ℝ)
        (Real.pi / 2) :=
    scalarFourierLaplacePlemelj_upperSineDamping_intervalIntegrable
      c (0 : ℝ) (Real.pi / 2)
  have hright :
      IntervalIntegrable
        (fun θ : ℝ => Real.exp (-(c * Real.sin θ)))
        MeasureTheory.volume
        (Real.pi / 2)
        Real.pi :=
    scalarFourierLaplacePlemelj_upperSineDamping_intervalIntegrable
      c (Real.pi / 2) Real.pi
  exact
    (intervalIntegral.integral_add_adjacent_intervals hleft hright).symm

/-- Pointwise reflection identity for the sine-damping integrand. -/
theorem scalarFourierLaplacePlemelj_upperSineDamping_pi_sub_eq
    (c θ : ℝ) :
    Real.exp (-(c * Real.sin (Real.pi - θ))) =
      Real.exp (-(c * Real.sin θ)) := by
  exact congrArg
    (fun r : ℝ => Real.exp (-(c * r)))
    (Real.sin_pi_sub θ)

/-- Endpoint transport for reflecting the right half interval. -/
theorem scalarFourierLaplacePlemelj_upperSineDamping_reflectedEndpointIntegral_eq
    (c : ℝ) :
    (∫ θ in (Real.pi - Real.pi / 2)..(Real.pi - 0),
        Real.exp (-(c * Real.sin θ))) =
      ∫ θ in (Real.pi / 2)..Real.pi,
        Real.exp (-(c * Real.sin θ)) := by
  have hleft : Real.pi - Real.pi / 2 = Real.pi / 2 :=
    sub_half Real.pi
  have hright : Real.pi - 0 = Real.pi :=
    sub_zero Real.pi
  exact congrArg₂
    (fun u v : ℝ =>
      ∫ θ in u..v, Real.exp (-(c * Real.sin θ)))
    hleft
    hright

/-- Reflection of the upper sine-damping right half onto the left half. -/
theorem scalarFourierLaplacePlemelj_upperSineDampingIntegral_rightHalf_eq_leftHalf
    (c : ℝ) :
    ∫ θ in (Real.pi / 2)..Real.pi,
        Real.exp (-(c * Real.sin θ)) =
      ∫ θ in (0 : ℝ)..(Real.pi / 2),
        Real.exp (-(c * Real.sin θ)) := by
  calc
    ∫ θ in (Real.pi / 2)..Real.pi,
        Real.exp (-(c * Real.sin θ)) =
        ∫ θ in (Real.pi - Real.pi / 2)..(Real.pi - 0),
          Real.exp (-(c * Real.sin θ)) := by
      exact
        (scalarFourierLaplacePlemelj_upperSineDamping_reflectedEndpointIntegral_eq
          c).symm
    _ = ∫ θ in (0 : ℝ)..(Real.pi / 2),
        Real.exp (-(c * Real.sin (Real.pi - θ))) := by
      exact
        (intervalIntegral.integral_comp_sub_left
          (f := fun θ : ℝ => Real.exp (-(c * Real.sin θ)))
          (a := (0 : ℝ))
          (b := Real.pi / 2)
          (d := Real.pi)).symm
    _ = ∫ θ in (0 : ℝ)..(Real.pi / 2),
        Real.exp (-(c * Real.sin θ)) := by
      exact intervalIntegral.integral_congr
        (fun θ _hθ =>
          scalarFourierLaplacePlemelj_upperSineDamping_pi_sub_eq c θ)

/-- Symmetry of the upper semicircle sine-damping integral around `π / 2`. -/
theorem scalarFourierLaplacePlemelj_upperSineDampingIntegral_eq_two_half
    (c : ℝ) :
    ∫ θ in (0 : ℝ)..Real.pi,
        Real.exp (-(c * Real.sin θ)) =
      2 * ∫ θ in (0 : ℝ)..(Real.pi / 2),
        Real.exp (-(c * Real.sin θ)) := by
  let L : ℝ :=
    ∫ θ in (0 : ℝ)..(Real.pi / 2),
      Real.exp (-(c * Real.sin θ))
  calc
    ∫ θ in (0 : ℝ)..Real.pi,
        Real.exp (-(c * Real.sin θ)) =
        L +
        ∫ θ in (Real.pi / 2)..Real.pi,
          Real.exp (-(c * Real.sin θ)) := by
      exact scalarFourierLaplacePlemelj_upperSineDampingIntegral_split_half c
    _ = L + L := by
      exact congrArg
        (fun r : ℝ => L + r)
        (scalarFourierLaplacePlemelj_upperSineDampingIntegral_rightHalf_eq_leftHalf
          c)
    _ = 2 * L := by
      exact (two_mul L).symm

/-- Jordan lower bound converted into an upper bound for the upper half
sine-damping exponential. -/
theorem scalarFourierLaplacePlemelj_upperSineDamping_integrand_le_linearExp
    (c θ : ℝ) (hc : 0 < c)
    (hθ0 : 0 ≤ θ) (hθhalf : θ ≤ Real.pi / 2) :
    Real.exp (-(c * Real.sin θ)) ≤
      Real.exp (-(((2 * c) / Real.pi) * θ)) := by
  have hsin : (2 / Real.pi : ℝ) * θ ≤ Real.sin θ :=
    Real.mul_le_sin hθ0 hθhalf
  have hmul : c * ((2 / Real.pi : ℝ) * θ) ≤ c * Real.sin θ :=
    mul_le_mul_of_nonneg_left hsin hc.le
  have halg :
      ((2 * c) / Real.pi) * θ =
        c * ((2 / Real.pi : ℝ) * θ) := by
    calc
      ((2 * c) / Real.pi) * θ =
          ((2 * c) * Real.pi⁻¹) * θ := by
        exact congrArg
          (fun r : ℝ => r * θ)
          (div_eq_mul_inv (2 * c) Real.pi)
      _ = (c * (2 * Real.pi⁻¹)) * θ := by
        have htwo_c : 2 * c = c * 2 :=
          mul_comm 2 c
        exact congrArg
          (fun r : ℝ => (r * Real.pi⁻¹) * θ)
          htwo_c
      _ = c * ((2 * Real.pi⁻¹) * θ) := by
        exact mul_assoc c (2 * Real.pi⁻¹) θ
      _ = c * ((2 / Real.pi : ℝ) * θ) := by
        exact congrArg
          (fun r : ℝ => c * (r * θ))
          (div_eq_mul_inv 2 Real.pi).symm
  have harg :
      -(c * Real.sin θ) ≤ -(((2 * c) / Real.pi) * θ) := by
    exact neg_le_neg
      (halg.trans_le hmul)
  exact Real.exp_le_exp.mpr harg

/-- Elementary exponential integral bound on the upper half interval. -/
theorem scalarFourierLaplacePlemelj_upperLinearExp_integral_eq_scaled_one_sub_exp
    (c : ℝ) (hc : 0 < c) :
    ∫ θ in (0 : ℝ)..(Real.pi / 2),
        Real.exp (-(((2 * c) / Real.pi) * θ)) =
      ((Real.pi / 2) * c⁻¹) * (1 - Real.exp (-c)) := by
  let k : ℝ := (2 * c) / Real.pi
  let A : ℝ := (Real.pi / 2) * c⁻¹
  have hpi_ne : Real.pi ≠ 0 :=
    Real.pi_pos.ne'
  have hc_ne : c ≠ 0 :=
    hc.ne'
  have hk_pos : 0 < k := by
    exact div_pos (mul_pos zero_lt_two hc) Real.pi_pos
  have hk_ne : k ≠ 0 :=
    hk_pos.ne'
  have harg :
      (fun θ : ℝ => Real.exp (-(((2 * c) / Real.pi) * θ))) =
        fun θ : ℝ => Real.exp ((-k) * θ) := by
    exact funext
      (fun θ : ℝ =>
        calc
          Real.exp (-(((2 * c) / Real.pi) * θ)) =
              Real.exp (-(k * θ)) := by
            exact congrArg Real.exp
              (congrArg Neg.neg
                (congrArg (fun r : ℝ => r * θ) rfl))
          _ = Real.exp ((-k) * θ) := by
            exact congrArg Real.exp
              (neg_mul k θ).symm)
  have hendpoint_zero : (-k) * (0 : ℝ) = 0 :=
    mul_zero (-k)
  have hendpoint_half : (-k) * (Real.pi / 2) = -c := by
    calc
      (-k) * (Real.pi / 2) =
          -(k * (Real.pi / 2)) := by
        exact neg_mul k (Real.pi / 2)
      _ = -(((2 * c) / Real.pi) * (Real.pi / 2)) := by
        exact congrArg Neg.neg
          (congrArg (fun r : ℝ => r * (Real.pi / 2)) rfl)
      _ = -(((2 * c) * Real.pi⁻¹) * (Real.pi / 2)) := by
        exact congrArg Neg.neg
          (congrArg (fun r : ℝ => r * (Real.pi / 2))
            (div_eq_mul_inv (2 * c) Real.pi))
      _ = -((2 * c) * (Real.pi⁻¹ * (Real.pi / 2))) := by
        exact congrArg Neg.neg
          (mul_assoc (2 * c) Real.pi⁻¹ (Real.pi / 2))
      _ = -((2 * c) * ((Real.pi⁻¹ * Real.pi) / 2)) := by
        exact congrArg
          (fun r : ℝ => -((2 * c) * r))
          (mul_div_assoc Real.pi⁻¹ Real.pi 2).symm
      _ = -((2 * c) * (1 / 2)) := by
        exact congrArg
          (fun r : ℝ => -((2 * c) * (r / 2)))
          (inv_mul_cancel₀ hpi_ne)
      _ = -(((2 * c) / 2)) := by
        exact congrArg Neg.neg
          (mul_div_assoc 2 c 2)
      _ = -c := by
        exact congrArg Neg.neg
          (mul_div_cancel_left₀ c two_ne_zero)
  have hscale_mul_k : A * k = 1 := by
    calc
      A * k =
          ((Real.pi / 2) * c⁻¹) * ((2 * c) / Real.pi) := by
        exact rfl
      _ = ((Real.pi / 2) * c⁻¹) * ((2 * c) * Real.pi⁻¹) := by
        exact congrArg
          (fun r : ℝ => ((Real.pi / 2) * c⁻¹) * r)
          (div_eq_mul_inv (2 * c) Real.pi)
      _ = (Real.pi / 2) * (c⁻¹ * ((2 * c) * Real.pi⁻¹)) := by
        exact mul_assoc (Real.pi / 2) c⁻¹ ((2 * c) * Real.pi⁻¹)
      _ = (Real.pi / 2) * ((c⁻¹ * (2 * c)) * Real.pi⁻¹) := by
        exact congrArg
          (fun r : ℝ => (Real.pi / 2) * r)
          (mul_assoc c⁻¹ (2 * c) Real.pi⁻¹)
      _ = (Real.pi / 2) * (((c⁻¹ * c) * 2) * Real.pi⁻¹) := by
        have htwo_c : 2 * c = c * 2 :=
          mul_comm 2 c
        have hstep :
            c⁻¹ * (2 * c) = (c⁻¹ * c) * 2 := by
          calc
            c⁻¹ * (2 * c) = c⁻¹ * (c * 2) := by
              exact congrArg (fun r : ℝ => c⁻¹ * r) htwo_c
            _ = (c⁻¹ * c) * 2 := by
              exact mul_assoc c⁻¹ c 2
        exact congrArg
          (fun r : ℝ => (Real.pi / 2) * (r * Real.pi⁻¹))
          hstep
      _ = (Real.pi / 2) * ((1 * 2) * Real.pi⁻¹) := by
        exact congrArg
          (fun r : ℝ => (Real.pi / 2) * ((r * 2) * Real.pi⁻¹))
          (inv_mul_cancel₀ hc_ne)
      _ = (Real.pi / 2) * (2 * Real.pi⁻¹) := by
        exact congrArg
          (fun r : ℝ => (Real.pi / 2) * (r * Real.pi⁻¹))
          (one_mul 2)
      _ = ((Real.pi / 2) * 2) * Real.pi⁻¹ := by
        exact (mul_assoc (Real.pi / 2) 2 Real.pi⁻¹).symm
      _ = Real.pi * Real.pi⁻¹ := by
        exact congrArg
          (fun r : ℝ => r * Real.pi⁻¹)
          (div_mul_cancel₀ Real.pi two_ne_zero)
      _ = 1 := by
        exact mul_inv_cancel₀ hpi_ne
  have hneg_inv : (-k)⁻¹ = -A := by
    have hmul : (-A) * (-k) = 1 := by
      calc
        (-A) * (-k) = A * k := by
          exact neg_mul_neg A k
        _ = 1 := hscale_mul_k
    exact eq_inv_of_mul_eq_one_left hmul
  have hintegral :
      ∫ θ in (0 : ℝ)..(Real.pi / 2), Real.exp ((-k) * θ) =
        (-k)⁻¹ *
          (Real.exp ((-k) * (Real.pi / 2)) -
            Real.exp ((-k) * (0 : ℝ))) := by
    calc
      ∫ θ in (0 : ℝ)..(Real.pi / 2), Real.exp ((-k) * θ) =
          (-k)⁻¹ •
            ∫ y in ((-k) * (0 : ℝ))..((-k) * (Real.pi / 2)),
              Real.exp y := by
        exact intervalIntegral.integral_comp_mul_left
          (f := Real.exp)
          (a := (0 : ℝ))
          (b := Real.pi / 2)
          (c := -k)
          (neg_ne_zero.mpr hk_ne)
      _ =
          (-k)⁻¹ *
            (Real.exp ((-k) * (Real.pi / 2)) -
              Real.exp ((-k) * (0 : ℝ))) := by
        exact congrArg
          (fun r : ℝ => (-k)⁻¹ * r)
          (integral_exp
            (a := (-k) * (0 : ℝ))
            (b := (-k) * (Real.pi / 2)))
  calc
    ∫ θ in (0 : ℝ)..(Real.pi / 2),
        Real.exp (-(((2 * c) / Real.pi) * θ)) =
        ∫ θ in (0 : ℝ)..(Real.pi / 2), Real.exp ((-k) * θ) := by
      exact congrArg
        (fun f : ℝ → ℝ => ∫ θ in (0 : ℝ)..(Real.pi / 2), f θ)
        harg
    _ =
        (-k)⁻¹ *
          (Real.exp ((-k) * (Real.pi / 2)) -
            Real.exp ((-k) * (0 : ℝ))) := by
      exact hintegral
    _ = (-A) * (Real.exp (-c) - Real.exp ((-k) * (0 : ℝ))) := by
      exact congrArg₂
        (fun u v : ℝ =>
          u * (Real.exp v - Real.exp ((-k) * (0 : ℝ))))
        hneg_inv
        hendpoint_half
    _ = (-A) * (Real.exp (-c) - Real.exp 0) := by
      exact congrArg
        (fun r : ℝ => (-A) * (Real.exp (-c) - Real.exp r))
        hendpoint_zero
    _ = (-A) * (Real.exp (-c) - 1) := by
      exact congrArg
        (fun r : ℝ => (-A) * (Real.exp (-c) - r))
        Real.exp_zero
    _ = A * (1 - Real.exp (-c)) := by
      calc
        (-A) * (Real.exp (-c) - 1) =
            A * (-(Real.exp (-c) - 1)) := by
          exact neg_mul_eq_mul_neg A (Real.exp (-c) - 1)
        _ = A * (1 - Real.exp (-c)) := by
          exact congrArg
            (fun r : ℝ => A * r)
            (neg_sub (Real.exp (-c)) 1)
    _ = ((Real.pi / 2) * c⁻¹) * (1 - Real.exp (-c)) := by
      exact rfl

/-- The finite exponential loss factor is bounded by one. -/
theorem scalarFourierLaplacePlemelj_one_sub_exp_neg_le_one
    (c : ℝ) :
    1 - Real.exp (-c) ≤ 1 := by
  exact sub_le_self 1 (Real.exp_pos (-c)).le

/-- The scale factor in the elementary exponential integral is nonnegative. -/
theorem scalarFourierLaplacePlemelj_upperLinearExp_scale_nonneg
    (c : ℝ) (hc : 0 < c) :
    0 ≤ (Real.pi / 2) * c⁻¹ := by
  have hhalf_nonneg : 0 ≤ Real.pi / 2 :=
    half_nonneg Real.pi_nonneg
  have hinv_nonneg : 0 ≤ c⁻¹ :=
    inv_nonneg.mpr hc.le
  exact mul_nonneg hhalf_nonneg hinv_nonneg

/-- Elementary exponential integral bound on the upper half interval. -/
theorem scalarFourierLaplacePlemelj_upperLinearExp_integral_le
    (c : ℝ) (hc : 0 < c) :
    ∫ θ in (0 : ℝ)..(Real.pi / 2),
        Real.exp (-(((2 * c) / Real.pi) * θ)) ≤
      (Real.pi / 2) * c⁻¹ := by
  calc
    ∫ θ in (0 : ℝ)..(Real.pi / 2),
        Real.exp (-(((2 * c) / Real.pi) * θ)) =
        ((Real.pi / 2) * c⁻¹) * (1 - Real.exp (-c)) := by
      exact
        scalarFourierLaplacePlemelj_upperLinearExp_integral_eq_scaled_one_sub_exp
          c hc
    _ ≤ ((Real.pi / 2) * c⁻¹) * 1 := by
      exact mul_le_mul_of_nonneg_left
        (scalarFourierLaplacePlemelj_one_sub_exp_neg_le_one c)
        (scalarFourierLaplacePlemelj_upperLinearExp_scale_nonneg c hc)
    _ = (Real.pi / 2) * c⁻¹ := by
      exact mul_one ((Real.pi / 2) * c⁻¹)

/-- Pointwise Jordan's inequality integrates to comparison with the elementary
linear exponential on the upper half interval. -/
theorem scalarFourierLaplacePlemelj_upperSineDamping_halfIntegral_le_linearExpIntegral
    (c : ℝ) (hc : 0 < c) :
    ∫ θ in (0 : ℝ)..(Real.pi / 2),
        Real.exp (-(c * Real.sin θ)) ≤
      ∫ θ in (0 : ℝ)..(Real.pi / 2),
        Real.exp (-(((2 * c) / Real.pi) * θ)) := by
  have hhalf_nonneg : (0 : ℝ) ≤ Real.pi / 2 :=
    half_nonneg Real.pi_nonneg
  have hsine_cont :
      Continuous
        (fun θ : ℝ => Real.exp (-(c * Real.sin θ))) := by
    have harg :
        Continuous
          (fun θ : ℝ => -(c * Real.sin θ)) := by
      exact (continuous_const.mul Real.continuous_sin).neg
    exact Real.continuous_exp.comp harg
  have hlinear_cont :
      Continuous
        (fun θ : ℝ => Real.exp (-(((2 * c) / Real.pi) * θ))) := by
    have harg :
        Continuous
          (fun θ : ℝ => -(((2 * c) / Real.pi) * θ)) := by
      exact (continuous_const.mul continuous_id).neg
    exact Real.continuous_exp.comp harg
  have hsine_int :
      IntervalIntegrable
        (fun θ : ℝ => Real.exp (-(c * Real.sin θ)))
        MeasureTheory.volume
        (0 : ℝ)
        (Real.pi / 2) :=
    hsine_cont.intervalIntegrable (0 : ℝ) (Real.pi / 2)
  have hlinear_int :
      IntervalIntegrable
        (fun θ : ℝ => Real.exp (-(((2 * c) / Real.pi) * θ)))
        MeasureTheory.volume
        (0 : ℝ)
        (Real.pi / 2) :=
    hlinear_cont.intervalIntegrable (0 : ℝ) (Real.pi / 2)
  exact intervalIntegral.integral_mono_on
    hhalf_nonneg
    hsine_int
    hlinear_int
    (fun θ hθ =>
      scalarFourierLaplacePlemelj_upperSineDamping_integrand_le_linearExp
        c θ hc hθ.1 hθ.2)

/-- Upper half-interval Jordan sine-damping integral bound. -/
theorem scalarFourierLaplacePlemelj_upperSineDamping_halfIntegral_le
    (c : ℝ) (hc : 0 < c) :
    ∫ θ in (0 : ℝ)..(Real.pi / 2),
        Real.exp (-(c * Real.sin θ)) ≤
      (Real.pi / 2) * c⁻¹ := by
  exact
    (scalarFourierLaplacePlemelj_upperSineDamping_halfIntegral_le_linearExpIntegral
      c hc).trans
      (scalarFourierLaplacePlemelj_upperLinearExp_integral_le c hc)

/-- The doubled half-interval majorant is the full Jordan majorant. -/
theorem scalarFourierLaplacePlemelj_two_mul_upperHalfMajorant_eq
    (c : ℝ) :
    2 * ((Real.pi / 2) * c⁻¹) = Real.pi * c⁻¹ := by
  calc
    2 * ((Real.pi / 2) * c⁻¹) =
        (2 * (Real.pi / 2)) * c⁻¹ := by
      exact mul_assoc 2 (Real.pi / 2) c⁻¹
    _ = ((2 * Real.pi) / 2) * c⁻¹ := by
      exact congrArg
        (fun r : ℝ => r * c⁻¹)
        (mul_div_assoc 2 Real.pi 2).symm
    _ = Real.pi * c⁻¹ := by
      have htwo_ne : (2 : ℝ) ≠ 0 :=
        two_ne_zero
      have hcancel : (2 * Real.pi) / 2 = Real.pi := by
        exact mul_div_cancel_left₀ Real.pi htwo_ne
      exact congrArg
        (fun r : ℝ => r * c⁻¹)
        hcancel

/-- Full upper semicircle Jordan sine-damping integral bound. -/
theorem scalarFourierLaplacePlemelj_upperSineDamping_integral_le
    (c : ℝ) (hc : 0 < c) :
    ∫ θ in (0 : ℝ)..Real.pi,
        Real.exp (-(c * Real.sin θ)) ≤
      Real.pi * c⁻¹ := by
  calc
    ∫ θ in (0 : ℝ)..Real.pi,
        Real.exp (-(c * Real.sin θ)) =
        2 * ∫ θ in (0 : ℝ)..(Real.pi / 2),
          Real.exp (-(c * Real.sin θ)) := by
      exact scalarFourierLaplacePlemelj_upperSineDampingIntegral_eq_two_half c
    _ ≤ 2 * ((Real.pi / 2) * c⁻¹) := by
      exact mul_le_mul_of_nonneg_left
        (scalarFourierLaplacePlemelj_upperSineDamping_halfIntegral_le c hc)
        (by exact zero_le_two)
    _ = Real.pi * c⁻¹ := by
      exact scalarFourierLaplacePlemelj_two_mul_upperHalfMajorant_eq c

/-- Jordan's sine estimate for the positive upper-arc damping integral. -/
theorem scalarFourierLaplacePlemelj_positiveUpperArc_sineDampingIntegral_le
    (T x : ℝ) (hTx : 0 < T * x) :
    ∫ θ in (0 : ℝ)..Real.pi,
        Real.exp (-(T * x * Real.sin θ)) ≤
      Real.pi * (T * x)⁻¹ := by
  exact
    scalarFourierLaplacePlemelj_upperSineDamping_integral_le
      (T * x) hTx

/-- Multiplication by the positive Jordan prefactor transports the scalar
sine-damping estimate to the full density. -/
theorem scalarFourierLaplacePlemelj_positiveUpperArcJordanDensity_integral_le_majorant_of_sine
    (a : ℝ) (ha : 0 < a) (x : ℝ) (hx : x ∈ Set.Ioi (0 : ℝ))
    (T : ℝ) (hT : a < T)
    (hsine :
      ∫ θ in (0 : ℝ)..Real.pi,
          Real.exp (-(T * x * Real.sin θ)) ≤
        Real.pi * (T * x)⁻¹) :
    ∫ θ in (0 : ℝ)..Real.pi,
        scalarFourierLaplacePlemelj_positiveUpperArcJordanDensity a x T θ ≤
      scalarFourierLaplacePlemelj_positiveUpperArcJordanMajorant a x T := by
  have hTpos : 0 < T :=
    ha.trans hT
  have hdenpos : 0 < T - a :=
    sub_pos.mpr hT
  have hpref_nonneg : 0 ≤ T / (T - a) :=
    div_nonneg hTpos.le hdenpos.le
  calc
    ∫ θ in (0 : ℝ)..Real.pi,
        scalarFourierLaplacePlemelj_positiveUpperArcJordanDensity a x T θ =
        (T / (T - a)) *
          ∫ θ in (0 : ℝ)..Real.pi,
            Real.exp (-(T * x * Real.sin θ)) := by
      exact
        scalarFourierLaplacePlemelj_positiveUpperArcJordanDensity_integral_eq_prefactor_mul
          a T x
    _ ≤ (T / (T - a)) * (Real.pi * (T * x)⁻¹) := by
      exact mul_le_mul_of_nonneg_left hsine hpref_nonneg
    _ = (Real.pi * T / (T - a)) * (T * x)⁻¹ := by
      exact
        scalarFourierLaplacePlemelj_jordanPrefactor_mul_pi_inv_eq_majorant
          a T (T * x)
    _ = scalarFourierLaplacePlemelj_positiveUpperArcJordanMajorant a x T := by
      exact rfl

/-- Integral form of Jordan's sine estimate for the positive upper arc. -/
theorem scalarFourierLaplacePlemelj_positiveUpperArcJordanDensity_integral_le_majorant
    (a : ℝ) (ha : 0 < a) (x : ℝ) (hx : x ∈ Set.Ioi (0 : ℝ))
    (T : ℝ) (hT : a < T) :
    ∫ θ in (0 : ℝ)..Real.pi,
        scalarFourierLaplacePlemelj_positiveUpperArcJordanDensity a x T θ ≤
      scalarFourierLaplacePlemelj_positiveUpperArcJordanMajorant a x T := by
  have hTpos : 0 < T :=
    ha.trans hT
  have hxpos : 0 < x :=
    Set.mem_Ioi.mp hx
  have hTx : 0 < T * x :=
    mul_pos hTpos hxpos
  exact
    scalarFourierLaplacePlemelj_positiveUpperArcJordanDensity_integral_le_majorant_of_sine
      a ha x hx T hT
      (scalarFourierLaplacePlemelj_positiveUpperArc_sineDampingIntegral_le
        T x hTx)

/-- Interval-integral norm domination for the positive upper arc by the Jordan
density. -/
theorem scalarFourierLaplacePlemelj_positiveUpperArc_norm_le_jordanDensity_integral
    (a : ℝ) (ha : 0 < a) (x : ℝ) (hx : x ∈ Set.Ioi (0 : ℝ))
    (T : ℝ) (hT : a < T) :
    ‖scalarFourierLaplacePlemelj_positiveUpperArc a x T‖ ≤
      ∫ θ in (0 : ℝ)..Real.pi,
        scalarFourierLaplacePlemelj_positiveUpperArcJordanDensity a x T θ := by
  have hdensity_int :
      IntervalIntegrable
        (fun θ : ℝ =>
          scalarFourierLaplacePlemelj_positiveUpperArcJordanDensity a x T θ)
        MeasureTheory.volume
        (0 : ℝ)
        Real.pi :=
    scalarFourierLaplacePlemelj_positiveUpperArcJordanDensity_intervalIntegrable
      a x T
  have hnorm_abs :
      ‖∫ θ in (0 : ℝ)..Real.pi,
          scalarFourierLaplacePlemelj_positiveUpperArcIntegrand a x T θ‖ ≤
        |∫ θ in (0 : ℝ)..Real.pi,
          scalarFourierLaplacePlemelj_positiveUpperArcJordanDensity a x T θ| := by
    exact intervalIntegral.norm_integral_le_of_norm_le
      (Eventually.of_forall
        (fun θ _hθ =>
          scalarFourierLaplacePlemelj_positiveUpperArcIntegrand_norm_le_jordanDensity
            a ha x hx T hT θ))
      hdensity_int
  have hnonneg_integral :
      0 ≤ ∫ θ in (0 : ℝ)..Real.pi,
          scalarFourierLaplacePlemelj_positiveUpperArcJordanDensity a x T θ := by
    exact intervalIntegral.integral_nonneg
      Real.pi_nonneg
      (fun θ _hθ =>
        scalarFourierLaplacePlemelj_positiveUpperArcJordanDensity_nonneg
          a ha x T θ hT)
  calc
    ‖scalarFourierLaplacePlemelj_positiveUpperArc a x T‖ =
        ‖∫ θ in (0 : ℝ)..Real.pi,
          scalarFourierLaplacePlemelj_positiveUpperArcIntegrand a x T θ‖ := by
      exact congrArg norm
        (scalarFourierLaplacePlemelj_positiveUpperArc_eq_integral_integrand
          a x T)
    _ ≤ |∫ θ in (0 : ℝ)..Real.pi,
          scalarFourierLaplacePlemelj_positiveUpperArcJordanDensity a x T θ| := by
      exact hnorm_abs
    _ = ∫ θ in (0 : ℝ)..Real.pi,
          scalarFourierLaplacePlemelj_positiveUpperArcJordanDensity a x T θ := by
      exact abs_of_nonneg hnonneg_integral

/-- The positive upper arc is eventually bounded by the Jordan majorant. -/
theorem scalarFourierLaplacePlemelj_positiveUpperArc_norm_eventually_le_jordanMajorant
    (a : ℝ) (ha : 0 < a) (x : ℝ) (hx : x ∈ Set.Ioi (0 : ℝ)) :
    ∀ᶠ T in atTop,
      ‖scalarFourierLaplacePlemelj_positiveUpperArc a x T‖ ≤
        scalarFourierLaplacePlemelj_positiveUpperArcJordanMajorant a x T := by
  exact
    (eventually_gt_atTop a).mono
      (fun T hT =>
        (scalarFourierLaplacePlemelj_positiveUpperArc_norm_le_jordanDensity_integral
          a ha x hx T hT).trans
          (scalarFourierLaplacePlemelj_positiveUpperArcJordanDensity_integral_le_majorant
            a ha x hx T hT))

/-- Jordan norm estimate for the positive upper semicircle correction. -/
theorem scalarFourierLaplacePlemelj_positiveUpperArc_norm_tendsto_zero_jordanEstimate
    (a : ℝ) (ha : 0 < a) (x : ℝ) (hx : x ∈ Set.Ioi (0 : ℝ)) :
    Tendsto
      (fun T : ℝ => ‖scalarFourierLaplacePlemelj_positiveUpperArc a x T‖)
      atTop
      (𝓝 0) := by
  exact squeeze_zero'
    (Eventually.of_forall
      (fun T : ℝ =>
        norm_nonneg (scalarFourierLaplacePlemelj_positiveUpperArc a x T)))
    (scalarFourierLaplacePlemelj_positiveUpperArc_norm_eventually_le_jordanMajorant
      a ha x hx)
    (scalarFourierLaplacePlemelj_positiveUpperArcJordanMajorant_tendsto_zero
      a ha x hx)

/-- The upper semicircle correction term vanishes for positive time. -/
theorem scalarFourierLaplacePlemelj_positiveUpperArc_tendsto_zero
    (a : ℝ) (ha : 0 < a) (x : ℝ) (hx : x ∈ Set.Ioi (0 : ℝ)) :
    Tendsto
      (fun T : ℝ => scalarFourierLaplacePlemelj_positiveUpperArc a x T)
      atTop
      (𝓝 0) := by
  exact tendsto_zero_iff_norm_tendsto_zero.mpr
    (scalarFourierLaplacePlemelj_positiveUpperArc_norm_tendsto_zero_jordanEstimate
      a ha x hx)

/-- Positive-time finite-window contour limit before multiplying by the
compensating `exp (a x)` factor. -/
theorem scalarFourierLaplacePlemelj_positive_window_tendsto_residueValue
    (a : ℝ) (ha : 0 < a) (x : ℝ) (hx : x ∈ Set.Ioi (0 : ℝ)) :
    Tendsto
      (fun T : ℝ =>
        ∫ t in Set.Icc (-T) T,
          (-1 / ((a : ℂ) + t * Complex.I)) *
            Complex.exp
              (Complex.I * (t : ℂ) * (x : ℂ)))
      atTop
      (𝓝
        ((-2 * (Real.pi : ℂ)) *
          Complex.exp (-(a : ℂ) * (x : ℂ)))) := by
  let W : ℝ → ℂ :=
    fun T : ℝ =>
      ∫ t in Set.Icc (-T) T,
        (-1 / ((a : ℂ) + t * Complex.I)) *
          Complex.exp
            (Complex.I * (t : ℂ) * (x : ℂ))
  let A : ℝ → ℂ :=
    fun T : ℝ => scalarFourierLaplacePlemelj_positiveUpperArc a x T
  let R : ℂ :=
    (-2 * (Real.pi : ℂ)) *
      Complex.exp (-(a : ℂ) * (x : ℂ))
  have hsum_eventual :
      ∀ᶠ T in atTop, W T + A T = R := by
    unfold W
    unfold A
    unfold R
    exact
      scalarFourierLaplacePlemelj_positive_window_add_upperArc_eq_residueValue
        a ha x hx
  have hsum :
      Tendsto (fun T : ℝ => W T + A T) atTop (𝓝 R) :=
    tendsto_nhds_of_eventually_eq hsum_eventual
  have hnegA :
      Tendsto (fun T : ℝ => -A T) atTop (𝓝 0) := by
    have hA :
        Tendsto A atTop (𝓝 0) := by
      unfold A
      exact
        scalarFourierLaplacePlemelj_positiveUpperArc_tendsto_zero
          a ha x hx
    exact Eq.subst
      (motive := fun z : ℂ =>
        Tendsto (fun T : ℝ => -A T) atTop (𝓝 z))
      neg_zero
      hA.neg
  have hW :
      Tendsto (fun T : ℝ => W T + A T + -A T) atTop (𝓝 (R + 0)) :=
    hsum.add hnegA
  have hpoint :
      (fun T : ℝ => W T + A T + -A T) = W := by
    funext T
    calc
      W T + A T + -A T = W T + (A T + -A T) := by
        exact add_assoc (W T) (A T) (-A T)
      _ = W T + 0 := by
        exact congrArg (fun z : ℂ => W T + z) (add_neg_cancel (A T))
      _ = W T := by
        exact add_zero (W T)
  have htarget : R + 0 = R :=
    add_zero R
  exact Eq.subst
    (motive := fun u : ℝ → ℂ => Tendsto u atTop (𝓝 R))
    hpoint
    (Eq.subst
      (motive := fun z : ℂ =>
        Tendsto (fun T : ℝ => W T + A T + -A T) atTop (𝓝 z))
      htarget
      hW)

/-- Multiplying a convergent positive-time residue window by `exp (a x)`. -/
theorem scalarFourierLaplacePlemelj_positive_window_tendsto_residueValue_mul_exp
    (a : ℝ) (ha : 0 < a) (x : ℝ) (hx : x ∈ Set.Ioi (0 : ℝ)) :
    Tendsto
      (fun T : ℝ =>
        (∫ t in Set.Icc (-T) T,
          (-1 / ((a : ℂ) + t * Complex.I)) *
            Complex.exp
              (Complex.I * (t : ℂ) * (x : ℂ))) *
          Complex.exp ((a : ℂ) * (x : ℂ)))
      atTop
      (𝓝
        (((-2 * (Real.pi : ℂ)) *
          Complex.exp (-(a : ℂ) * (x : ℂ))) *
          Complex.exp ((a : ℂ) * (x : ℂ)))) := by
  exact
    (scalarFourierLaplacePlemelj_positive_window_tendsto_residueValue
      a ha x hx).mul
      (tendsto_const_nhds :
        Tendsto
          (fun _T : ℝ => Complex.exp ((a : ℂ) * (x : ℂ)))
          atTop
          (𝓝 (Complex.exp ((a : ℂ) * (x : ℂ)))))

/-- Pointwise algebra moving the compensating exponential inside the
positive-time finite window. -/
theorem scalarFourierLaplacePlemelj_positive_window_mul_exp_eq_window_with_exp
    (a : ℝ) (x T : ℝ) :
    (∫ t in Set.Icc (-T) T,
      (-1 / ((a : ℂ) + t * Complex.I)) *
        Complex.exp
          (Complex.I * (t : ℂ) * (x : ℂ))) *
      Complex.exp ((a : ℂ) * (x : ℂ)) =
    ∫ t in Set.Icc (-T) T,
      (-1 / ((a : ℂ) + t * Complex.I)) *
        Complex.exp
          (Complex.I * (t : ℂ) * (x : ℂ)) *
        Complex.exp ((a : ℂ) * (x : ℂ)) := by
  exact (intervalIntegral.integral_mul_const
    (f := fun t : ℝ =>
      (-1 / ((a : ℂ) + t * Complex.I)) *
        Complex.exp
          (Complex.I * (t : ℂ) * (x : ℂ)))
    (c := Complex.exp ((a : ℂ) * (x : ℂ)))
    (-T) T).symm

/-- Positive-time residue limit after moving the compensating exponential
inside the symmetric finite window. -/
theorem scalarFourierLaplacePlemelj_positive_window_tendsto_residueValue_with_exp
    (a : ℝ) (ha : 0 < a) (x : ℝ) (hx : x ∈ Set.Ioi (0 : ℝ)) :
    Tendsto
      (fun T : ℝ =>
        ∫ t in Set.Icc (-T) T,
          (-1 / ((a : ℂ) + t * Complex.I)) *
            Complex.exp
              (Complex.I * (t : ℂ) * (x : ℂ)) *
            Complex.exp ((a : ℂ) * (x : ℂ)))
      atTop
      (𝓝
        (((-2 * (Real.pi : ℂ)) *
          Complex.exp (-(a : ℂ) * (x : ℂ))) *
          Complex.exp ((a : ℂ) * (x : ℂ)))) := by
  exact Eq.subst
    (motive := fun u : ℝ → ℂ =>
      Tendsto u atTop
        (𝓝
          (((-2 * (Real.pi : ℂ)) *
            Complex.exp (-(a : ℂ) * (x : ℂ))) *
            Complex.exp ((a : ℂ) * (x : ℂ)))))
    (funext
      (fun T : ℝ =>
        scalarFourierLaplacePlemelj_positive_window_mul_exp_eq_window_with_exp
          a x T))
    (scalarFourierLaplacePlemelj_positive_window_tendsto_residueValue_mul_exp
      a ha x hx)

/-- Positive-time scalar Plemelj window after the Laplace denominator has been
evaluated by the one-sided exponential transform. -/
theorem scalarFourierLaplacePlemelj_positive_window_tendsto_laplaceJump
    (a : ℝ) (ha : 0 < a) (x : ℝ) (hx : x ∈ Set.Ioi (0 : ℝ)) :
    Tendsto
      (fun T : ℝ =>
        ∫ t in Set.Icc (-T) T,
          (-1 / ((a : ℂ) + t * Complex.I)) *
            Complex.exp
              (Complex.I * (t : ℂ) * (x : ℂ)) *
            Complex.exp ((a : ℂ) * (x : ℂ)))
      atTop
      (𝓝
        ((-2 * (Real.pi : ℂ)) *
          Complex.exp (-(a : ℂ) * (x : ℂ)) *
          Complex.exp ((a : ℂ) * (x : ℂ)))) := by
  exact
    scalarFourierLaplacePlemelj_positive_window_tendsto_residueValue_with_exp
      a ha x hx

/-- The positive-time Laplace jump collapses after multiplying by the compensating
`exp (a x)` factor. -/
theorem scalarFourierLaplacePlemelj_positive_laplaceJump_mul_eq_constant
    (a : ℝ) (x : ℝ) :
    ((-2 * (Real.pi : ℂ)) *
        Complex.exp (-(a : ℂ) * (x : ℂ)) *
        Complex.exp ((a : ℂ) * (x : ℂ))) =
      (-2 * (Real.pi : ℂ)) := by
  have hsum :
      (-(a : ℂ) * (x : ℂ)) + ((a : ℂ) * (x : ℂ)) = 0 :=
    neg_add_cancel ((a : ℂ) * (x : ℂ))
  have hexp :
      Complex.exp (-(a : ℂ) * (x : ℂ)) *
          Complex.exp ((a : ℂ) * (x : ℂ)) =
        1 := by
    calc
      Complex.exp (-(a : ℂ) * (x : ℂ)) *
          Complex.exp ((a : ℂ) * (x : ℂ))
          = Complex.exp
              ((-(a : ℂ) * (x : ℂ)) + ((a : ℂ) * (x : ℂ))) := by
            exact (Complex.exp_add (-(a : ℂ) * (x : ℂ))
              ((a : ℂ) * (x : ℂ))).symm
      _ = Complex.exp 0 := by
            exact congrArg Complex.exp hsum
      _ = 1 := by
            exact Complex.exp_zero
  calc
    ((-2 * (Real.pi : ℂ)) *
        Complex.exp (-(a : ℂ) * (x : ℂ)) *
        Complex.exp ((a : ℂ) * (x : ℂ)))
        =
        (-2 * (Real.pi : ℂ)) *
          (Complex.exp (-(a : ℂ) * (x : ℂ)) *
            Complex.exp ((a : ℂ) * (x : ℂ))) := by
          exact mul_assoc (-2 * (Real.pi : ℂ))
            (Complex.exp (-(a : ℂ) * (x : ℂ)))
            (Complex.exp ((a : ℂ) * (x : ℂ)))
    _ = (-2 * (Real.pi : ℂ)) * 1 := by
          exact congrArg
            (fun z : ℂ => (-2 * (Real.pi : ℂ)) * z)
            hexp
    _ = (-2 * (Real.pi : ℂ)) := by
          exact mul_one (-2 * (Real.pi : ℂ))

/-- Positive-time normalized Fourier-Laplace Plemelj value. -/
theorem scalarFourierLaplacePlemelj_pointwise_positive
    (a : ℝ) (ha : 0 < a) (x : ℝ) (hx : x ∈ Set.Ioi (0 : ℝ)) :
    Tendsto
      (fun T : ℝ =>
        ∫ t in Set.Icc (-T) T,
          (-1 / ((a : ℂ) + t * Complex.I)) *
            Complex.exp
              (Complex.I * (t : ℂ) * (x : ℂ)) *
            Complex.exp ((a : ℂ) * (x : ℂ)))
      atTop
      (𝓝 (-2 * (Real.pi : ℂ))) := by
  exact Eq.subst
    (motive := fun y : ℂ =>
      Tendsto
        (fun T : ℝ =>
          ∫ t in Set.Icc (-T) T,
            (-1 / ((a : ℂ) + t * Complex.I)) *
              Complex.exp
                (Complex.I * (t : ℂ) * (x : ℂ)) *
              Complex.exp ((a : ℂ) * (x : ℂ)))
        atTop
        (𝓝 y))
    (scalarFourierLaplacePlemelj_positive_laplaceJump_mul_eq_constant a x)
    (scalarFourierLaplacePlemelj_positive_window_tendsto_laplaceJump
      a ha x hx)

/-- Lower semicircle correction term for the negative-time scalar
Fourier-Laplace contour.  The real segment runs from `-T` to `T`, and this arc
returns from `T` to `-T` through the lower half-plane. -/
noncomputable def scalarFourierLaplacePlemelj_negativeLowerArc
    (a x T : ℝ) : ℂ :=
  ∫ θ in (0 : ℝ)..(-Real.pi),
    let z : ℂ := (T : ℂ) * Complex.exp (Complex.I * (θ : ℂ))
    (-1 / ((a : ℂ) + z * Complex.I)) *
      Complex.exp (Complex.I * z * (x : ℂ)) *
      (Complex.I * (T : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))

/-- Integrand of the negative lower semicircle correction. -/
noncomputable def scalarFourierLaplacePlemelj_negativeLowerArcIntegrand
    (a x T θ : ℝ) : ℂ :=
  let z : ℂ := (T : ℂ) * Complex.exp (Complex.I * (θ : ℂ))
  (-1 / ((a : ℂ) + z * Complex.I)) *
    Complex.exp (Complex.I * z * (x : ℂ)) *
    (Complex.I * (T : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))

/-- The negative lower arc is the interval integral of its named integrand. -/
theorem scalarFourierLaplacePlemelj_negativeLowerArc_eq_integral_integrand
    (a x T : ℝ) :
    scalarFourierLaplacePlemelj_negativeLowerArc a x T =
      ∫ θ in (0 : ℝ)..(-Real.pi),
        scalarFourierLaplacePlemelj_negativeLowerArcIntegrand a x T θ := by
  rfl

/-- Real Jordan density for the negative lower semicircle estimate. -/
noncomputable def scalarFourierLaplacePlemelj_negativeLowerArcJordanDensity
    (a x T θ : ℝ) : ℝ :=
  (T / (T - a)) * Real.exp (-(T * x * Real.sin θ))

/-- Closed lower-half-plane scalar contour integral for the negative-time
Fourier-Laplace denominator. -/
noncomputable def scalarFourierLaplacePlemelj_negativeClosedContour
    (a x T : ℝ) : ℂ :=
  (∫ t in Set.Icc (-T) T,
    (-1 / ((a : ℂ) + t * Complex.I)) *
      Complex.exp
        (Complex.I * (t : ℂ) * (x : ℂ))) +
    scalarFourierLaplacePlemelj_negativeLowerArc a x T

/-- The negative closed contour unfolds to its real segment plus lower arc. -/
theorem scalarFourierLaplacePlemelj_negativeClosedContour_eq_window_add_lowerArc
    (a x T : ℝ) :
    scalarFourierLaplacePlemelj_negativeClosedContour a x T =
      (∫ t in Set.Icc (-T) T,
        (-1 / ((a : ℂ) + t * Complex.I)) *
          Complex.exp
            (Complex.I * (t : ℂ) * (x : ℂ))) +
          scalarFourierLaplacePlemelj_negativeLowerArc a x T := by
  rfl

/-- The upper scalar pole is outside the lower half-plane contour. -/
theorem scalarFourierLaplacePlemelj_upperPole_not_mem_lowerSemicircleInterior
    (a : ℝ) (ha : 0 < a) (T : ℝ) (hT : 0 < T) :
    ¬ scalarFourierLaplacePlemelj_upperPole a =
        (-(a : ℂ)) * Complex.I := by
  intro hpole
  have him :
      Complex.im (scalarFourierLaplacePlemelj_upperPole a) =
        Complex.im ((-(a : ℂ)) * Complex.I) :=
    congrArg Complex.im hpole
  have hleft :
      Complex.im (scalarFourierLaplacePlemelj_upperPole a) = a := by
    calc
      Complex.im (scalarFourierLaplacePlemelj_upperPole a) =
          Complex.im ((a : ℂ) * Complex.I) := by
        exact congrArg Complex.im
          (scalarFourierLaplacePlemelj_upperPole_eq a)
      _ = (a : ℂ).re * Complex.I.im + (a : ℂ).im * Complex.I.re := by
        exact Complex.mul_im (a : ℂ) Complex.I
      _ = a * 1 + 0 * 0 := by
        exact congrArg₂ HAdd.hAdd
          (congrArg₂ HMul.hMul
            (Complex.ofReal_re a)
            Complex.I_im)
          (congrArg₂ HMul.hMul
            (Complex.ofReal_im a)
            Complex.I_re)
      _ = a * 1 := by
        exact add_zero (a * 1)
      _ = a := by
        exact mul_one a
  have hright :
      Complex.im ((-(a : ℂ)) * Complex.I) = -a := by
    calc
      Complex.im ((-(a : ℂ)) * Complex.I) =
          (-(a : ℂ)).re * Complex.I.im + (-(a : ℂ)).im * Complex.I.re := by
        exact Complex.mul_im (-(a : ℂ)) Complex.I
      _ = (-(a : ℂ)).re * 1 + (-(a : ℂ)).im * 0 := by
        exact congrArg₂ HAdd.hAdd
          (congrArg₂ HMul.hMul
            rfl
            Complex.I_im)
          (congrArg₂ HMul.hMul
            rfl
            Complex.I_re)
      _ = (-(a : ℂ)).re * 1 + 0 := by
        exact congrArg
          (fun y : ℝ => (-(a : ℂ)).re * 1 + y)
          (mul_zero (-(a : ℂ)).im)
      _ = (-(a : ℂ)).re * 1 := by
        exact add_zero ((-(a : ℂ)).re * 1)
      _ = (-(a : ℂ)).re := by
        exact mul_one (-(a : ℂ)).re
      _ = -a := by
        exact (Complex.neg_re (a : ℂ)).trans
          (congrArg Neg.neg (Complex.ofReal_re a))
  have ha_eq_neg : a = -a :=
    hleft.symm.trans (him.trans hright)
  have htwo_zero : (2 : ℝ) * a = 0 := by
    have hadd : a + a = 0 :=
      eq_neg_iff_add_eq_zero.mp ha_eq_neg
    exact (two_mul a).symm.trans hadd
  have ha_zero : a = 0 :=
    (mul_eq_zero.mp htwo_zero).resolve_left two_ne_zero
  exact (ne_of_gt ha) ha_zero

/-- Owner pole-free residue theorem for the negative-time lower semicircle
contour. -/
theorem scalarFourierLaplacePlemelj_negativeClosedContour_eq_zero_owner
    (a : ℝ) (ha : 0 < a) (x : ℝ) (hx : x < 0)
    (T : ℝ)
    (_hpole :
      ¬ scalarFourierLaplacePlemelj_upperPole a =
          (-(a : ℂ)) * Complex.I) :
    scalarFourierLaplacePlemelj_negativeClosedContour a x T = 0 := by
  sorry

/-- Pole-free lower-half-plane contour integral for the negative-time scalar kernel. -/
theorem scalarFourierLaplacePlemelj_negativeClosedContour_eq_zero_of_noPole
    (a : ℝ) (ha : 0 < a) (x : ℝ) (hx : x < 0)
    (T : ℝ)
    (_hpole :
      ¬ scalarFourierLaplacePlemelj_upperPole a =
          (-(a : ℂ)) * Complex.I) :
    scalarFourierLaplacePlemelj_negativeClosedContour a x T = 0 := by
  exact
    scalarFourierLaplacePlemelj_negativeClosedContour_eq_zero_owner
      a ha x hx T _hpole

/-- Radius-qualified lower-half-plane pole-free residue theorem for the negative-time
scalar closed contour. -/
theorem scalarFourierLaplacePlemelj_negativeClosedContour_eq_zero_of_poleOutside
    (a : ℝ) (ha : 0 < a) (x : ℝ) (hx : x < 0)
    (T : ℝ) (hT : 0 < T) :
    scalarFourierLaplacePlemelj_negativeClosedContour a x T = 0 := by
  exact
    scalarFourierLaplacePlemelj_negativeClosedContour_eq_zero_of_noPole
      a ha x hx T
      (scalarFourierLaplacePlemelj_upperPole_not_mem_lowerSemicircleInterior
        a ha T hT)

/-- Lower-half-plane pole-free residue theorem for the negative-time scalar closed
contour. -/
theorem scalarFourierLaplacePlemelj_negativeClosedContour_eq_zero_residueTheorem
    (a : ℝ) (ha : 0 < a) (x : ℝ) (hx : x < 0) :
    ∀ᶠ T in atTop,
      scalarFourierLaplacePlemelj_negativeClosedContour a x T = 0 := by
  exact (eventually_gt_atTop (0 : ℝ)).mono
    (fun T hT =>
      scalarFourierLaplacePlemelj_negativeClosedContour_eq_zero_of_poleOutside
        a ha x hx T hT)

/-- Finite lower-half-plane pole-free contour identity for the negative-time
scalar Fourier-Laplace contour. -/
theorem scalarFourierLaplacePlemelj_negative_window_add_lowerArc_eq_zero
    (a : ℝ) (ha : 0 < a) (x : ℝ) (hx : x < 0) :
    ∀ᶠ T in atTop,
      (∫ t in Set.Icc (-T) T,
        (-1 / ((a : ℂ) + t * Complex.I)) *
          Complex.exp
            (Complex.I * (t : ℂ) * (x : ℂ))) +
          scalarFourierLaplacePlemelj_negativeLowerArc a x T =
        0 := by
  have hclosed :
      ∀ᶠ T in atTop,
        scalarFourierLaplacePlemelj_negativeClosedContour a x T = 0 :=
    scalarFourierLaplacePlemelj_negativeClosedContour_eq_zero_residueTheorem
      a ha x hx
  exact hclosed.mono
    (fun T hT =>
      (scalarFourierLaplacePlemelj_negativeClosedContour_eq_window_add_lowerArc
        a x T).symm.trans hT)

/-- Negative lower-arc Jordan majorant. -/
noncomputable def scalarFourierLaplacePlemelj_negativeLowerArcJordanMajorant
    (a x T : ℝ) : ℝ :=
  (Real.pi * T / (T - a)) * ((T * (-x))⁻¹)

/-- The negative lower-arc Jordan prefactor has a finite limit. -/
theorem scalarFourierLaplacePlemelj_negativeLowerArcJordanPrefactor_tendsto_pi
    (a : ℝ) :
    Tendsto
      (fun T : ℝ => Real.pi * T / (T - a))
      atTop
      (𝓝 Real.pi) :=
  scalarFourierLaplacePlemelj_positiveUpperArcJordanPrefactor_tendsto_pi a

/-- The negative lower-arc reciprocal linear factor tends to zero. -/
theorem scalarFourierLaplacePlemelj_negativeLowerArcJordanReciprocal_tendsto_zero
    (x : ℝ) (hx : x < 0) :
    Tendsto
      (fun T : ℝ => (T * (-x))⁻¹)
      atTop
      (𝓝 0) := by
  have hneg : 0 < -x :=
    neg_pos.mpr hx
  exact
    tendsto_inv_atTop_zero.comp
      (Tendsto.atTop_mul_const
        hneg
        tendsto_id)

/-- The negative lower-arc Jordan majorant tends to zero. -/
theorem scalarFourierLaplacePlemelj_negativeLowerArcJordanMajorant_tendsto_zero
    (a : ℝ) (ha : 0 < a) (x : ℝ) (hx : x < 0) :
    Tendsto
      (fun T : ℝ =>
        scalarFourierLaplacePlemelj_negativeLowerArcJordanMajorant a x T)
      atTop
      (𝓝 0) := by
  exact
    (scalarFourierLaplacePlemelj_negativeLowerArcJordanPrefactor_tendsto_pi
      a).mul
      (scalarFourierLaplacePlemelj_negativeLowerArcJordanReciprocal_tendsto_zero
        x hx)

/-- Denominator part of the negative lower-arc Jordan pointwise estimate. -/
theorem scalarFourierLaplacePlemelj_negativeLowerArc_denominator_norm_inv_le
    (a : ℝ) (ha : 0 < a) (T : ℝ) (hT : a < T) (θ : ℝ) :
    ‖(-1 /
      ((a : ℂ) +
        ((T : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) * Complex.I))‖ ≤
      (T - a)⁻¹ := by
  exact
    scalarFourierLaplacePlemelj_semicircleDenominator_inv_norm_le
      a ha T hT θ

/-- Exponential damping part of the negative lower-arc Jordan pointwise estimate. -/
theorem scalarFourierLaplacePlemelj_negativeLowerArc_exponential_norm_eq_damping
    (x T θ : ℝ) :
    ‖Complex.exp
      (Complex.I *
        ((T : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) *
        (x : ℂ))‖ =
      Real.exp (-(T * x * Real.sin θ)) := by
  exact
    scalarFourierLaplacePlemelj_positiveUpperArc_exponential_norm_eq_damping
      x T θ

/-- Velocity part of the negative lower-arc Jordan pointwise estimate. -/
theorem scalarFourierLaplacePlemelj_negativeLowerArc_velocity_norm_eq_radius
    (a : ℝ) (ha : 0 < a) (T : ℝ) (hT : a < T) (θ : ℝ) :
    ‖Complex.I * (T : ℂ) * Complex.exp (Complex.I * (θ : ℂ))‖ = T := by
  exact
    scalarFourierLaplacePlemelj_semicircleVelocity_norm_eq_radius
      T (ha.trans hT) θ

/-- Product assembly for the negative lower-arc Jordan pointwise estimate. -/
theorem scalarFourierLaplacePlemelj_negativeLowerArcIntegrand_norm_le_jordanDensity_of_factors
    (a : ℝ) (ha : 0 < a) (x : ℝ) (hx : x < 0)
    (T : ℝ) (hT : a < T) (θ : ℝ)
    (hden :
      ‖(-1 /
        ((a : ℂ) +
          ((T : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) * Complex.I))‖ ≤
        (T - a)⁻¹)
    (hexp :
      ‖Complex.exp
        (Complex.I *
          ((T : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) *
          (x : ℂ))‖ =
        Real.exp (-(T * x * Real.sin θ)))
    (hvel :
      ‖Complex.I * (T : ℂ) * Complex.exp (Complex.I * (θ : ℂ))‖ = T) :
    ‖scalarFourierLaplacePlemelj_negativeLowerArcIntegrand a x T θ‖ ≤
      scalarFourierLaplacePlemelj_negativeLowerArcJordanDensity a x T θ := by
  let D : ℂ :=
    -1 /
      ((a : ℂ) +
        ((T : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) * Complex.I)
  let E : ℂ :=
    Complex.exp
      (Complex.I *
        ((T : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) *
        (x : ℂ))
  let V : ℂ :=
    Complex.I * (T : ℂ) * Complex.exp (Complex.I * (θ : ℂ))
  let R : ℝ :=
    Real.exp (-(T * x * Real.sin θ))
  have hER : ‖E‖ = R := by
    exact hexp
  have hVR : ‖V‖ = T := by
    exact hvel
  have hV_nonneg : 0 ≤ ‖V‖ :=
    norm_nonneg V
  have hstep :
      (‖D‖ * ‖E‖) * ‖V‖ ≤
        ((T - a)⁻¹ * ‖E‖) * ‖V‖ := by
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hden (norm_nonneg E))
      hV_nonneg
  calc
    ‖scalarFourierLaplacePlemelj_negativeLowerArcIntegrand a x T θ‖ =
        ‖D * E * V‖ := by
      exact rfl
    _ = ‖D * E‖ * ‖V‖ := by
      exact norm_mul (D * E) V
    _ = (‖D‖ * ‖E‖) * ‖V‖ := by
      exact congrArg
        (fun r : ℝ => r * ‖V‖)
        (norm_mul D E)
    _ ≤ ((T - a)⁻¹ * ‖E‖) * ‖V‖ := by
      exact hstep
    _ = ((T - a)⁻¹ * R) * ‖V‖ := by
      exact congrArg
        (fun r : ℝ => ((T - a)⁻¹ * r) * ‖V‖)
        hER
    _ = ((T - a)⁻¹ * R) * T := by
      exact congrArg
        (fun r : ℝ => ((T - a)⁻¹ * R) * r)
        hVR
    _ = (T / (T - a)) * R := by
      exact
        (scalarFourierLaplacePlemelj_jordanDensity_eq_inv_mul_exp_mul_radius
          a T R).symm
    _ = scalarFourierLaplacePlemelj_negativeLowerArcJordanDensity a x T θ := by
      exact rfl

/-- Pointwise Jordan domination of the negative lower-arc integrand. -/
theorem scalarFourierLaplacePlemelj_negativeLowerArcIntegrand_norm_le_jordanDensity
    (a : ℝ) (ha : 0 < a) (x : ℝ) (hx : x < 0)
    (T : ℝ) (hT : a < T) (θ : ℝ) :
    ‖scalarFourierLaplacePlemelj_negativeLowerArcIntegrand a x T θ‖ ≤
      scalarFourierLaplacePlemelj_negativeLowerArcJordanDensity a x T θ := by
  exact
    scalarFourierLaplacePlemelj_negativeLowerArcIntegrand_norm_le_jordanDensity_of_factors
      a ha x hx T hT θ
      (scalarFourierLaplacePlemelj_negativeLowerArc_denominator_norm_inv_le
        a ha T hT θ)
      (scalarFourierLaplacePlemelj_negativeLowerArc_exponential_norm_eq_damping
        x T θ)
      (scalarFourierLaplacePlemelj_negativeLowerArc_velocity_norm_eq_radius
        a ha T hT θ)

/-- The negative lower-arc Jordan density is interval-integrable. -/
theorem scalarFourierLaplacePlemelj_negativeLowerArcJordanDensity_intervalIntegrable
    (a x T : ℝ) :
    IntervalIntegrable
      (fun θ : ℝ =>
        scalarFourierLaplacePlemelj_negativeLowerArcJordanDensity a x T θ)
      MeasureTheory.volume
      (-Real.pi)
      (0 : ℝ) := by
  have harg :
      Continuous
        (fun θ : ℝ => -(T * x * Real.sin θ)) := by
    exact (continuous_const.mul Real.continuous_sin).neg
  have hexp :
      Continuous
        (fun θ : ℝ => Real.exp (-(T * x * Real.sin θ))) := by
    exact Real.continuous_exp.comp harg
  have hdensity :
      Continuous
        (fun θ : ℝ =>
          scalarFourierLaplacePlemelj_negativeLowerArcJordanDensity a x T θ) := by
    exact continuous_const.mul hexp
  exact hdensity.intervalIntegrable (-Real.pi) (0 : ℝ)

/-- The negative lower-arc Jordan density is nonnegative when the radius is
larger than the pole height. -/
theorem scalarFourierLaplacePlemelj_negativeLowerArcJordanDensity_nonneg
    (a : ℝ) (ha : 0 < a) (x T θ : ℝ) (hT : a < T) :
    0 ≤ scalarFourierLaplacePlemelj_negativeLowerArcJordanDensity a x T θ := by
  have hTpos : 0 < T :=
    ha.trans hT
  have hdenpos : 0 < T - a :=
    sub_pos.mpr hT
  have hpref_nonneg : 0 ≤ T / (T - a) :=
    div_nonneg hTpos.le hdenpos.le
  exact mul_nonneg hpref_nonneg (Real.exp_pos _).le

/-- The negative Jordan density interval integral factors into the constant
prefactor times the scalar lower-arc sine-damping integral. -/
theorem scalarFourierLaplacePlemelj_negativeLowerArcJordanDensity_integral_eq_prefactor_mul
    (a : ℝ) (T x : ℝ) :
    ∫ θ in (-Real.pi)..(0 : ℝ),
        scalarFourierLaplacePlemelj_negativeLowerArcJordanDensity a x T θ =
      (T / (T - a)) *
        ∫ θ in (-Real.pi)..(0 : ℝ),
          Real.exp (-(T * x * Real.sin θ)) := by
  exact intervalIntegral.integral_const_mul
    (T / (T - a))
    (fun θ : ℝ => Real.exp (-(T * x * Real.sin θ)))

/-- The lower-arc damping integrand after `θ ↦ -θ` is the upper-arc damping
integrand for `-x`. -/
theorem scalarFourierLaplacePlemelj_lowerSineDamping_negIntegrand_eq_upper
    (T x θ : ℝ) :
    Real.exp (-(T * x * Real.sin (-θ))) =
      Real.exp (-((T * (-x)) * Real.sin θ)) := by
  have hleft_arg :
      -(T * x * Real.sin (-θ)) =
        T * x * Real.sin θ := by
    calc
      -(T * x * Real.sin (-θ)) =
          -(T * x * (-Real.sin θ)) := by
        exact congrArg
          (fun r : ℝ => -(T * x * r))
          (Real.sin_neg θ)
      _ = -((T * x) * (-Real.sin θ)) := by
        exact rfl
      _ = -(-(T * x * Real.sin θ)) := by
        exact congrArg Neg.neg
          (mul_neg (T * x) (Real.sin θ))
      _ = T * x * Real.sin θ := by
        exact neg_neg (T * x * Real.sin θ)
  have hright_arg :
      -((T * (-x)) * Real.sin θ) =
        T * x * Real.sin θ := by
    calc
      -((T * (-x)) * Real.sin θ) =
          -((-(T * x)) * Real.sin θ) := by
        exact congrArg
          (fun r : ℝ => -(r * Real.sin θ))
          (mul_neg T x)
      _ = -(-(T * x * Real.sin θ)) := by
        exact congrArg Neg.neg
          (neg_mul (T * x) (Real.sin θ))
      _ = T * x * Real.sin θ := by
        exact neg_neg (T * x * Real.sin θ)
  exact congrArg Real.exp
    (hleft_arg.trans hright_arg.symm)

/-- Lower semicircle sine-damping integral is transported to the upper
semicircle by `θ ↦ -θ`. -/
theorem scalarFourierLaplacePlemelj_lowerSineDampingIntegral_eq_upper
    (T x : ℝ) :
    ∫ θ in (-Real.pi)..(0 : ℝ),
        Real.exp (-(T * x * Real.sin θ)) =
      ∫ θ in (0 : ℝ)..Real.pi,
        Real.exp (-((T * (-x)) * Real.sin θ)) := by
  calc
    ∫ θ in (-Real.pi)..(0 : ℝ),
        Real.exp (-(T * x * Real.sin θ)) =
        ∫ θ in (0 : ℝ)..Real.pi,
          Real.exp (-(T * x * Real.sin (-θ))) := by
      exact
        (intervalIntegral.integral_comp_neg
          (f := fun θ : ℝ => Real.exp (-(T * x * Real.sin θ)))
          (a := (0 : ℝ))
          (b := Real.pi)).symm
    _ = ∫ θ in (0 : ℝ)..Real.pi,
        Real.exp (-((T * (-x)) * Real.sin θ)) := by
      exact intervalIntegral.integral_congr
        (fun θ _hθ =>
          scalarFourierLaplacePlemelj_lowerSineDamping_negIntegrand_eq_upper
            T x θ)

/-- Jordan's sine estimate for the negative lower-arc damping integral. -/
theorem scalarFourierLaplacePlemelj_negativeLowerArc_sineDampingIntegral_le
    (T x : ℝ) (hTnegx : 0 < T * (-x)) :
    ∫ θ in (-Real.pi)..(0 : ℝ),
        Real.exp (-(T * x * Real.sin θ)) ≤
      Real.pi * (T * (-x))⁻¹ := by
  calc
    ∫ θ in (-Real.pi)..(0 : ℝ),
        Real.exp (-(T * x * Real.sin θ)) =
        ∫ θ in (0 : ℝ)..Real.pi,
          Real.exp (-((T * (-x)) * Real.sin θ)) := by
      exact scalarFourierLaplacePlemelj_lowerSineDampingIntegral_eq_upper
        T x
    _ ≤ Real.pi * (T * (-x))⁻¹ := by
      exact scalarFourierLaplacePlemelj_upperSineDamping_integral_le
        (T * (-x)) hTnegx

/-- Multiplication by the positive Jordan prefactor transports the scalar
lower-arc sine-damping estimate to the full density. -/
theorem scalarFourierLaplacePlemelj_negativeLowerArcJordanDensity_integral_le_majorant_of_sine
    (a : ℝ) (ha : 0 < a) (x : ℝ) (hx : x < 0)
    (T : ℝ) (hT : a < T)
    (hsine :
      ∫ θ in (-Real.pi)..(0 : ℝ),
          Real.exp (-(T * x * Real.sin θ)) ≤
        Real.pi * (T * (-x))⁻¹) :
    ∫ θ in (-Real.pi)..(0 : ℝ),
        scalarFourierLaplacePlemelj_negativeLowerArcJordanDensity a x T θ ≤
      scalarFourierLaplacePlemelj_negativeLowerArcJordanMajorant a x T := by
  have hTpos : 0 < T :=
    ha.trans hT
  have hdenpos : 0 < T - a :=
    sub_pos.mpr hT
  have hpref_nonneg : 0 ≤ T / (T - a) :=
    div_nonneg hTpos.le hdenpos.le
  calc
    ∫ θ in (-Real.pi)..(0 : ℝ),
        scalarFourierLaplacePlemelj_negativeLowerArcJordanDensity a x T θ =
        (T / (T - a)) *
          ∫ θ in (-Real.pi)..(0 : ℝ),
            Real.exp (-(T * x * Real.sin θ)) := by
      exact
        scalarFourierLaplacePlemelj_negativeLowerArcJordanDensity_integral_eq_prefactor_mul
          a T x
    _ ≤ (T / (T - a)) * (Real.pi * (T * (-x))⁻¹) := by
      exact mul_le_mul_of_nonneg_left hsine hpref_nonneg
    _ = (Real.pi * T / (T - a)) * (T * (-x))⁻¹ := by
      exact
        scalarFourierLaplacePlemelj_jordanPrefactor_mul_pi_inv_eq_majorant
          a T (T * (-x))
    _ = scalarFourierLaplacePlemelj_negativeLowerArcJordanMajorant a x T := by
      exact rfl

/-- Integral form of Jordan's sine estimate for the negative lower arc. -/
theorem scalarFourierLaplacePlemelj_negativeLowerArcJordanDensity_integral_le_majorant
    (a : ℝ) (ha : 0 < a) (x : ℝ) (hx : x < 0)
    (T : ℝ) (hT : a < T) :
    ∫ θ in (-Real.pi)..(0 : ℝ),
        scalarFourierLaplacePlemelj_negativeLowerArcJordanDensity a x T θ ≤
      scalarFourierLaplacePlemelj_negativeLowerArcJordanMajorant a x T := by
  have hTpos : 0 < T :=
    ha.trans hT
  have hnegx : 0 < -x :=
    neg_pos.mpr hx
  have hTnegx : 0 < T * (-x) :=
    mul_pos hTpos hnegx
  exact
    scalarFourierLaplacePlemelj_negativeLowerArcJordanDensity_integral_le_majorant_of_sine
      a ha x hx T hT
      (scalarFourierLaplacePlemelj_negativeLowerArc_sineDampingIntegral_le
        T x hTnegx)

/-- Interval-integral norm domination for the negative lower arc by the Jordan
density. -/
theorem scalarFourierLaplacePlemelj_negativeLowerArc_norm_le_jordanDensity_integral
    (a : ℝ) (ha : 0 < a) (x : ℝ) (hx : x < 0)
    (T : ℝ) (hT : a < T) :
    ‖scalarFourierLaplacePlemelj_negativeLowerArc a x T‖ ≤
      ∫ θ in (-Real.pi)..(0 : ℝ),
        scalarFourierLaplacePlemelj_negativeLowerArcJordanDensity a x T θ := by
  have hdensity_int :
      IntervalIntegrable
        (fun θ : ℝ =>
          scalarFourierLaplacePlemelj_negativeLowerArcJordanDensity a x T θ)
        MeasureTheory.volume
        (-Real.pi)
        (0 : ℝ) :=
    scalarFourierLaplacePlemelj_negativeLowerArcJordanDensity_intervalIntegrable
      a x T
  have hnorm_abs :
      ‖∫ θ in (-Real.pi)..(0 : ℝ),
          scalarFourierLaplacePlemelj_negativeLowerArcIntegrand a x T θ‖ ≤
        |∫ θ in (-Real.pi)..(0 : ℝ),
          scalarFourierLaplacePlemelj_negativeLowerArcJordanDensity a x T θ| := by
    exact intervalIntegral.norm_integral_le_of_norm_le
      (Eventually.of_forall
        (fun θ _hθ =>
          scalarFourierLaplacePlemelj_negativeLowerArcIntegrand_norm_le_jordanDensity
            a ha x hx T hT θ))
      hdensity_int
  have hneg_pi_le_zero : -Real.pi ≤ (0 : ℝ) :=
    neg_nonpos.mpr Real.pi_nonneg
  have hnonneg_integral :
      0 ≤ ∫ θ in (-Real.pi)..(0 : ℝ),
          scalarFourierLaplacePlemelj_negativeLowerArcJordanDensity a x T θ := by
    exact intervalIntegral.integral_nonneg
      hneg_pi_le_zero
      (fun θ _hθ =>
        scalarFourierLaplacePlemelj_negativeLowerArcJordanDensity_nonneg
          a ha x T θ hT)
  calc
    ‖scalarFourierLaplacePlemelj_negativeLowerArc a x T‖ =
        ‖∫ θ in (-Real.pi)..(0 : ℝ),
          scalarFourierLaplacePlemelj_negativeLowerArcIntegrand a x T θ‖ := by
      exact congrArg norm
        (scalarFourierLaplacePlemelj_negativeLowerArc_eq_integral_integrand
          a x T)
    _ ≤ |∫ θ in (-Real.pi)..(0 : ℝ),
          scalarFourierLaplacePlemelj_negativeLowerArcJordanDensity a x T θ| := by
      exact hnorm_abs
    _ = ∫ θ in (-Real.pi)..(0 : ℝ),
          scalarFourierLaplacePlemelj_negativeLowerArcJordanDensity a x T θ := by
      exact abs_of_nonneg hnonneg_integral

/-- The negative lower arc is eventually bounded by the Jordan majorant. -/
theorem scalarFourierLaplacePlemelj_negativeLowerArc_norm_eventually_le_jordanMajorant
    (a : ℝ) (ha : 0 < a) (x : ℝ) (hx : x < 0) :
    ∀ᶠ T in atTop,
      ‖scalarFourierLaplacePlemelj_negativeLowerArc a x T‖ ≤
        scalarFourierLaplacePlemelj_negativeLowerArcJordanMajorant a x T := by
  exact
    (eventually_gt_atTop a).mono
      (fun T hT =>
        (scalarFourierLaplacePlemelj_negativeLowerArc_norm_le_jordanDensity_integral
          a ha x hx T hT).trans
          (scalarFourierLaplacePlemelj_negativeLowerArcJordanDensity_integral_le_majorant
            a ha x hx T hT))

/-- Jordan norm estimate for the negative lower semicircle correction. -/
theorem scalarFourierLaplacePlemelj_negativeLowerArc_norm_tendsto_zero_jordanEstimate
    (a : ℝ) (ha : 0 < a) (x : ℝ) (hx : x < 0) :
    Tendsto
      (fun T : ℝ => ‖scalarFourierLaplacePlemelj_negativeLowerArc a x T‖)
      atTop
      (𝓝 0) := by
  exact squeeze_zero'
    (Eventually.of_forall
      (fun T : ℝ =>
        norm_nonneg (scalarFourierLaplacePlemelj_negativeLowerArc a x T)))
    (scalarFourierLaplacePlemelj_negativeLowerArc_norm_eventually_le_jordanMajorant
      a ha x hx)
    (scalarFourierLaplacePlemelj_negativeLowerArcJordanMajorant_tendsto_zero
      a ha x hx)

/-- The lower semicircle correction term vanishes for negative time. -/
theorem scalarFourierLaplacePlemelj_negativeLowerArc_tendsto_zero
    (a : ℝ) (ha : 0 < a) (x : ℝ) (hx : x < 0) :
    Tendsto
      (fun T : ℝ => scalarFourierLaplacePlemelj_negativeLowerArc a x T)
      atTop
      (𝓝 0) := by
  exact tendsto_zero_iff_norm_tendsto_zero.mpr
    (scalarFourierLaplacePlemelj_negativeLowerArc_norm_tendsto_zero_jordanEstimate
      a ha x hx)

/-- Negative-time finite-window contour limit before multiplying by the
constant `exp (a x)`. -/
theorem scalarFourierLaplacePlemelj_negative_window_tendsto_zero_without_exp
    (a : ℝ) (ha : 0 < a) (x : ℝ) (hx : x < 0) :
    Tendsto
      (fun T : ℝ =>
        ∫ t in Set.Icc (-T) T,
          (-1 / ((a : ℂ) + t * Complex.I)) *
            Complex.exp
              (Complex.I * (t : ℂ) * (x : ℂ)))
      atTop
      (𝓝 0) := by
  let W : ℝ → ℂ :=
    fun T : ℝ =>
      ∫ t in Set.Icc (-T) T,
        (-1 / ((a : ℂ) + t * Complex.I)) *
          Complex.exp
            (Complex.I * (t : ℂ) * (x : ℂ))
  let A : ℝ → ℂ :=
    fun T : ℝ => scalarFourierLaplacePlemelj_negativeLowerArc a x T
  have hsum_eventual :
      ∀ᶠ T in atTop, W T + A T = 0 := by
    unfold W
    unfold A
    exact
      scalarFourierLaplacePlemelj_negative_window_add_lowerArc_eq_zero
        a ha x hx
  have hsum :
      Tendsto (fun T : ℝ => W T + A T) atTop (𝓝 0) :=
    tendsto_nhds_of_eventually_eq hsum_eventual
  have hnegA :
      Tendsto (fun T : ℝ => -A T) atTop (𝓝 0) := by
    have hA :
        Tendsto A atTop (𝓝 0) := by
      unfold A
      exact
        scalarFourierLaplacePlemelj_negativeLowerArc_tendsto_zero
          a ha x hx
    exact Eq.subst
      (motive := fun z : ℂ =>
        Tendsto (fun T : ℝ => -A T) atTop (𝓝 z))
      neg_zero
      hA.neg
  have hW :
      Tendsto (fun T : ℝ => W T + A T + -A T) atTop (𝓝 (0 + 0 : ℂ)) :=
    hsum.add hnegA
  have hpoint :
      (fun T : ℝ => W T + A T + -A T) = W := by
    funext T
    calc
      W T + A T + -A T = W T + (A T + -A T) := by
        exact add_assoc (W T) (A T) (-A T)
      _ = W T + 0 := by
        exact congrArg (fun z : ℂ => W T + z) (add_neg_cancel (A T))
      _ = W T := by
        exact add_zero (W T)
  have htarget : (0 : ℂ) + 0 = 0 :=
    add_zero (0 : ℂ)
  exact Eq.subst
    (motive := fun u : ℝ → ℂ => Tendsto u atTop (𝓝 0))
    hpoint
    (Eq.subst
      (motive := fun z : ℂ =>
        Tendsto (fun T : ℝ => W T + A T + -A T) atTop (𝓝 z))
      htarget
      hW)

/-- Multiplication by `exp (a x)` preserves the negative-time zero limit. -/
theorem scalarFourierLaplacePlemelj_negative_window_tendsto_zero_mul_exp
    (a : ℝ) (ha : 0 < a) (x : ℝ) (hx : x < 0) :
    Tendsto
      (fun T : ℝ =>
        (∫ t in Set.Icc (-T) T,
          (-1 / ((a : ℂ) + t * Complex.I)) *
            Complex.exp
              (Complex.I * (t : ℂ) * (x : ℂ))) *
          Complex.exp ((a : ℂ) * (x : ℂ)))
      atTop
      (𝓝 0) := by
  have htarget :
      (0 : ℂ) * Complex.exp ((a : ℂ) * (x : ℂ)) = 0 :=
    zero_mul (Complex.exp ((a : ℂ) * (x : ℂ)))
  exact Eq.subst
    (motive := fun z : ℂ =>
      Tendsto
        (fun T : ℝ =>
          (∫ t in Set.Icc (-T) T,
            (-1 / ((a : ℂ) + t * Complex.I)) *
              Complex.exp
                (Complex.I * (t : ℂ) * (x : ℂ))) *
            Complex.exp ((a : ℂ) * (x : ℂ)))
        atTop
        (𝓝 z))
    htarget
    ((scalarFourierLaplacePlemelj_negative_window_tendsto_zero_without_exp
      a ha x hx).mul
      (tendsto_const_nhds :
        Tendsto
          (fun _T : ℝ => Complex.exp ((a : ℂ) * (x : ℂ)))
          atTop
          (𝓝 (Complex.exp ((a : ℂ) * (x : ℂ))))))

/-- Negative-time scalar Plemelj window after the Laplace denominator has been
closed on the pole-free side. -/
theorem scalarFourierLaplacePlemelj_negative_window_tendsto_zero
    (a : ℝ) (ha : 0 < a) (x : ℝ) (hx : x < 0) :
    Tendsto
      (fun T : ℝ =>
        ∫ t in Set.Icc (-T) T,
          (-1 / ((a : ℂ) + t * Complex.I)) *
            Complex.exp
              (Complex.I * (t : ℂ) * (x : ℂ)) *
            Complex.exp ((a : ℂ) * (x : ℂ)))
      atTop
      (𝓝 0) := by
  exact Eq.subst
    (motive := fun u : ℝ → ℂ =>
      Tendsto u atTop (𝓝 0))
    (funext
      (fun T : ℝ =>
        scalarFourierLaplacePlemelj_positive_window_mul_exp_eq_window_with_exp
          a x T))
    (scalarFourierLaplacePlemelj_negative_window_tendsto_zero_mul_exp
      a ha x hx)

/-- Negative-time normalized Fourier-Laplace Plemelj value. -/
theorem scalarFourierLaplacePlemelj_pointwise_negative
    (a : ℝ) (ha : 0 < a) (x : ℝ) (hx : x < 0) :
    Tendsto
      (fun T : ℝ =>
        ∫ t in Set.Icc (-T) T,
          (-1 / ((a : ℂ) + t * Complex.I)) *
            Complex.exp
              (Complex.I * (t : ℂ) * (x : ℂ)) *
            Complex.exp ((a : ℂ) * (x : ℂ)))
      atTop
      (𝓝 0) := by
  exact
    scalarFourierLaplacePlemelj_negative_window_tendsto_zero
      a ha x hx

/-- Off-endpoint pointwise normalized Fourier-Laplace Plemelj value.

For `a > 0`, the symmetric Fourier windows of
`-exp(a x)/(a + i t)` converge to the open half-line multiplier away from
the jump at `x = 0`. -/
theorem scalarFourierLaplacePlemelj_pointwise_openHalfLine
    (a : ℝ) (ha : 0 < a) (x : ℝ) (hx0 : x ≠ 0) :
    Tendsto
      (fun T : ℝ =>
        ∫ t in Set.Icc (-T) T,
          (-1 / ((a : ℂ) + t * Complex.I)) *
            Complex.exp
              (Complex.I * (t : ℂ) * (x : ℂ)) *
            Complex.exp ((a : ℂ) * (x : ℂ)))
      atTop
      (𝓝
        (Set.indicator (Set.Ioi (0 : ℝ))
          (fun _ : ℝ => (-2 * (Real.pi : ℂ))) x)) := by
  by_cases hx : x ∈ Set.Ioi (0 : ℝ)
  · have htarget :
        Set.indicator (Set.Ioi (0 : ℝ))
          (fun _ : ℝ => (-2 * (Real.pi : ℂ))) x =
            (-2 * (Real.pi : ℂ)) :=
      Set.indicator_of_mem hx _
    exact Eq.subst
      (motive := fun y : ℂ =>
        Tendsto
          (fun T : ℝ =>
            ∫ t in Set.Icc (-T) T,
              (-1 / ((a : ℂ) + t * Complex.I)) *
                Complex.exp
                  (Complex.I * (t : ℂ) * (x : ℂ)) *
                Complex.exp ((a : ℂ) * (x : ℂ)))
          atTop
          (𝓝 y))
      htarget.symm
      (scalarFourierLaplacePlemelj_pointwise_positive a ha x hx)
  · have htarget :
      Set.indicator (Set.Ioi (0 : ℝ))
          (fun _ : ℝ => (-2 * (Real.pi : ℂ))) x =
            0 :=
      Set.indicator_of_not_mem hx _
    have hxneg : x < 0 :=
      lt_of_le_of_ne (not_lt.mp hx) hx0
    exact Eq.subst
      (motive := fun y : ℂ =>
        Tendsto
          (fun T : ℝ =>
            ∫ t in Set.Icc (-T) T,
              (-1 / ((a : ℂ) + t * Complex.I)) *
                Complex.exp
                  (Complex.I * (t : ℂ) * (x : ℂ)) *
                Complex.exp ((a : ℂ) * (x : ℂ)))
          atTop
          (𝓝 y))
      htarget.symm
      (scalarFourierLaplacePlemelj_pointwise_negative a ha x hxneg)

/-- Normalized scalar finite-window Cauchy integral after multiplication by
the compensating exponential. -/
noncomputable def scalarFourierLaplacePlemelj_unweightedWindowMulExp
    (a T x : ℝ) : ℂ :=
  (∫ t in Set.Icc (-T) T,
    (-1 / ((a : ℂ) + t * Complex.I)) *
      Complex.exp
        (Complex.I * (t : ℂ) * (x : ℂ))) *
    Complex.exp ((a : ℂ) * (x : ℂ))

/-- The normalized scalar finite-window Cauchy integral unfolds to the window integral
times the compensating exponential. -/
theorem scalarFourierLaplacePlemelj_unweightedWindowMulExp_eq
    (a T x : ℝ) :
    scalarFourierLaplacePlemelj_unweightedWindowMulExp a T x =
      (∫ t in Set.Icc (-T) T,
        (-1 / ((a : ℂ) + t * Complex.I)) *
          Complex.exp
            (Complex.I * (t : ℂ) * (x : ℂ))) *
        Complex.exp ((a : ℂ) * (x : ℂ)) := by
  rfl

/-- The quadratic denominator in the zero-time Cauchy kernel is strictly
positive. -/
theorem scalarFourierLaplacePlemelj_zero_denominator_pos
    (a : ℝ) (ha : 0 < a) (t : ℝ) :
    0 < a ^ 2 + t ^ 2 :=
  add_pos_of_pos_of_nonneg (sq_pos_of_pos ha) (sq_nonneg t)

/-- The quadratic denominator in the zero-time Cauchy kernel is nonzero. -/
theorem scalarFourierLaplacePlemelj_zero_denominator_ne_zero
    (a : ℝ) (ha : 0 < a) (t : ℝ) :
    a ^ 2 + t ^ 2 ≠ 0 :=
  ne_of_gt
    (scalarFourierLaplacePlemelj_zero_denominator_pos a ha t)

/-- Pointwise algebraic decomposition of the zero-time Cauchy kernel into its
real even part and imaginary odd part. -/
theorem scalarFourierLaplacePlemelj_zero_kernel_pointwise_decomposition
    (a : ℝ) (ha : 0 < a) (t : ℝ) :
    (-1 / ((a : ℂ) + t * Complex.I)) =
      ((-(a / (a ^ 2 + t ^ 2)) : ℝ) : ℂ) +
        (((t / (a ^ 2 + t ^ 2) : ℝ) : ℂ) * Complex.I) := by
  have hden_pos : 0 < a ^ 2 + t ^ 2 :=
    scalarFourierLaplacePlemelj_zero_denominator_pos a ha t
  have hden_ne : a ^ 2 + t ^ 2 ≠ 0 :=
    ne_of_gt hden_pos
  have hz_ne : ((a : ℂ) + t * Complex.I) ≠ 0 := by
    intro hz
    have hre : (((a : ℂ) + t * Complex.I).re) = (0 : ℂ).re :=
      congrArg Complex.re hz
    have ha_zero : a = 0 := by
      simpa only [Complex.add_re, Complex.ofReal_re, Complex.mul_re,
        Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, mul_one,
        sub_zero, Complex.zero_re] using hre
    exact (ne_of_gt ha) ha_zero
  ext
  · field_simp [hz_ne, hden_ne]
    ring
  · field_simp [hz_ne, hden_ne]
    ring

/-- The odd imaginary part of the zero-time symmetric Cauchy window cancels. -/
theorem scalarFourierLaplacePlemelj_zero_odd_imaginary_integral_eq_zero
    (a : ℝ) (ha : 0 < a) (T : ℝ) :
    ∫ t in Set.Icc (-T) T,
      (((t / (a ^ 2 + t ^ 2) : ℝ) : ℂ) * Complex.I) = 0 := by
  let f : ℝ → ℂ :=
    fun t : ℝ => (((t / (a ^ 2 + t ^ 2) : ℝ) : ℂ) * Complex.I)
  have hodd : ∀ t : ℝ, f (-t) = -f t := by
    intro t
    unfold f
    have hden :
        a ^ 2 + (-t) ^ 2 = a ^ 2 + t ^ 2 := by
      ring
    calc
      ((((-t) / (a ^ 2 + (-t) ^ 2) : ℝ) : ℂ) * Complex.I)
          =
          ((((-t) / (a ^ 2 + t ^ 2) : ℝ) : ℂ) * Complex.I) := by
            exact congrArg
              (fun y : ℝ => ((y : ℂ) * Complex.I))
              (congrArg (fun d : ℝ => (-t) / d) hden)
      _ =
          -(((t / (a ^ 2 + t ^ 2) : ℝ) : ℂ) * Complex.I) := by
            ring
  have hcomp :
      (∫ t in (-T)..T, f (-t)) = ∫ t in (-T)..T, f t := by
    simpa only [neg_neg] using
      (intervalIntegral.integral_comp_neg (f := f) (a := -T) (b := T)).symm
  have hneg :
      (∫ t in (-T)..T, f (-t)) = -∫ t in (-T)..T, f t := by
    calc
      (∫ t in (-T)..T, f (-t))
          = ∫ t in (-T)..T, -f t := by
            exact intervalIntegral.integral_congr
              (Filter.Eventually.of_forall hodd)
      _ = -∫ t in (-T)..T, f t := by
            exact intervalIntegral.integral_neg
  have hself_neg : (∫ t in (-T)..T, f t) = -∫ t in (-T)..T, f t :=
    hcomp.symm.trans hneg
  have htwo_zero : (2 : ℂ) * (∫ t in (-T)..T, f t) = 0 := by
    have hsum_zero :
        (∫ t in (-T)..T, f t) + (∫ t in (-T)..T, f t) = 0 := by
      calc
        (∫ t in (-T)..T, f t) + (∫ t in (-T)..T, f t)
            =
            -(∫ t in (-T)..T, f t) + (∫ t in (-T)..T, f t) := by
              exact congrArg
                (fun z : ℂ => z + (∫ t in (-T)..T, f t))
                hself_neg
        _ = 0 := by
            exact neg_add_cancel (∫ t in (-T)..T, f t)
    exact (two_mul (∫ t in (-T)..T, f t)).trans hsum_zero
  have htwo_ne : (2 : ℂ) ≠ 0 :=
    two_ne_zero
  exact mul_eq_zero.mp htwo_zero |>.resolve_left htwo_ne

/-- The even real part of the zero-time symmetric Cauchy window has the
arctangent primitive value. -/
theorem scalarFourierLaplacePlemelj_zero_real_kernel_integral_eq_arctan
    (a : ℝ) (ha : 0 < a) (T : ℝ) :
    ∫ t in Set.Icc (-T) T,
      ((-(a / (a ^ 2 + t ^ 2)) : ℝ) : ℂ) =
      (-(2 : ℝ) * Real.arctan (T / a) : ℂ) := by
  have ha_ne : a ≠ 0 := ne_of_gt ha
  have hreal :
      (∫ t in (-T)..T, (-(a / (a ^ 2 + t ^ 2)) : ℝ)) =
        -(2 : ℝ) * Real.arctan (T / a) := by
    have hscale :
        (∫ u in (-(T / a))..(T / a),
          (-(1 : ℝ) / (1 + u ^ 2))) =
          -(2 : ℝ) * Real.arctan (T / a) := by
      calc
        (∫ u in (-(T / a))..(T / a),
          (-(1 : ℝ) / (1 + u ^ 2)))
            = -∫ u in (-(T / a))..(T / a),
                ((1 : ℝ) + u ^ 2)⁻¹ := by
              simp only [neg_div, one_div, intervalIntegral.integral_neg]
        _ = -(Real.arctan (T / a) - Real.arctan (-(T / a))) := by
              exact congrArg Neg.neg
                (Real.integral_inv_one_add_sq
                  (a := -(T / a)) (b := T / a))
        _ = -(2 : ℝ) * Real.arctan (T / a) := by
              rw [Real.arctan_neg]
              ring
    have hsub :
        (∫ t in (-T)..T, (-(a / (a ^ 2 + t ^ 2)) : ℝ)) =
          ∫ u in (-(T / a))..(T / a),
            (-(1 : ℝ) / (1 + u ^ 2)) := by
      have hcomp :=
        intervalIntegral.integral_comp_mul_left
          (f := fun t : ℝ => (-(a / (a ^ 2 + t ^ 2)) : ℝ))
          (a := -(T / a)) (b := T / a) ha_ne
      have hpoint :
          ∀ u : ℝ,
            (a⁻¹ : ℝ) • (-(a / (a ^ 2 + (a * u) ^ 2)) : ℝ) =
              (-(1 : ℝ) / (1 + u ^ 2)) := by
        intro u
        field_simp [ha_ne]
        ring
      calc
        (∫ t in (-T)..T, (-(a / (a ^ 2 + t ^ 2)) : ℝ))
            =
            (a⁻¹ : ℝ) •
              ∫ t in (a * (-(T / a)))..(a * (T / a)),
                (-(a / (a ^ 2 + t ^ 2)) : ℝ) := by
              rw [mul_neg, mul_div_cancel₀ T ha_ne,
                mul_div_cancel₀ T ha_ne]
              exact Eq.symm hcomp
        _ =
            ∫ u in (-(T / a))..(T / a),
              (a⁻¹ : ℝ) •
                (-(a / (a ^ 2 + (a * u) ^ 2)) : ℝ) := by
              rw [intervalIntegral.integral_smul]
        _ =
            ∫ u in (-(T / a))..(T / a),
              (-(1 : ℝ) / (1 + u ^ 2)) := by
              exact intervalIntegral.integral_congr
                (Filter.Eventually.of_forall hpoint)
    exact hsub.trans hscale
  calc
    (∫ t in Set.Icc (-T) T,
      ((-(a / (a ^ 2 + t ^ 2)) : ℝ) : ℂ))
        =
        ∫ t in (-T)..T,
          ((-(a / (a ^ 2 + t ^ 2)) : ℝ) : ℂ) := by
          rfl
    _ =
        ((∫ t in (-T)..T,
          (-(a / (a ^ 2 + t ^ 2)) : ℝ)) : ℂ) := by
          exact intervalIntegral.integral_ofReal
    _ =
        (-(2 : ℝ) * Real.arctan (T / a) : ℂ) := by
          exact congrArg (fun y : ℝ => (y : ℂ)) hreal

/-- Interval integrability of the even real part of the zero-time Cauchy
kernel on symmetric finite windows. -/
theorem scalarFourierLaplacePlemelj_zero_real_kernel_intervalIntegrable
    (a : ℝ) (ha : 0 < a) (T : ℝ) :
    IntervalIntegrable
      (fun t : ℝ => ((-(a / (a ^ 2 + t ^ 2)) : ℝ) : ℂ))
      volume (-T) T := by
  have hden_cont : Continuous (fun t : ℝ => a ^ 2 + t ^ 2) :=
    continuous_const.add (continuous_id.pow 2)
  have hquot_cont : Continuous (fun t : ℝ => a / (a ^ 2 + t ^ 2)) :=
    continuous_const.div hden_cont
      (scalarFourierLaplacePlemelj_zero_denominator_ne_zero a ha)
  have hreal_cont :
      Continuous (fun t : ℝ => (-(a / (a ^ 2 + t ^ 2)) : ℝ)) :=
    hquot_cont.neg
  exact (Complex.continuous_ofReal.comp hreal_cont).intervalIntegrable (-T) T

/-- Interval integrability of the odd imaginary part of the zero-time Cauchy
kernel on symmetric finite windows. -/
theorem scalarFourierLaplacePlemelj_zero_odd_imaginary_intervalIntegrable
    (a : ℝ) (ha : 0 < a) (T : ℝ) :
    IntervalIntegrable
      (fun t : ℝ => (((t / (a ^ 2 + t ^ 2) : ℝ) : ℂ) * Complex.I))
      volume (-T) T := by
  have hden_cont : Continuous (fun t : ℝ => a ^ 2 + t ^ 2) :=
    continuous_const.add (continuous_id.pow 2)
  have hquot_cont : Continuous (fun t : ℝ => t / (a ^ 2 + t ^ 2)) :=
    continuous_id.div hden_cont
      (scalarFourierLaplacePlemelj_zero_denominator_ne_zero a ha)
  have hcomplex_cont :
      Continuous
        (fun t : ℝ => ((t / (a ^ 2 + t ^ 2) : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.comp hquot_cont
  exact (hcomplex_cont.mul continuous_const).intervalIntegrable (-T) T

/-- Zero-time symmetric Cauchy window before multiplying by the trivial
endpoint exponential factors. -/
theorem scalarFourierLaplacePlemelj_zero_raw_window_eq_arctan
    (a : ℝ) (ha : 0 < a) (T : ℝ) :
    ∫ t in Set.Icc (-T) T,
      (-1 / ((a : ℂ) + t * Complex.I)) =
      (-(2 : ℝ) * Real.arctan (T / a) : ℂ) := by
  calc
    ∫ t in Set.Icc (-T) T,
        (-1 / ((a : ℂ) + t * Complex.I))
        =
        ∫ t in Set.Icc (-T) T,
          ((-(a / (a ^ 2 + t ^ 2)) : ℝ) : ℂ) +
            (((t / (a ^ 2 + t ^ 2) : ℝ) : ℂ) * Complex.I) := by
          exact intervalIntegral.integral_congr
            (Filter.Eventually.of_forall
              (fun t : ℝ =>
                scalarFourierLaplacePlemelj_zero_kernel_pointwise_decomposition
                  a ha t))
    _ =
        (∫ t in Set.Icc (-T) T,
          ((-(a / (a ^ 2 + t ^ 2)) : ℝ) : ℂ)) +
          ∫ t in Set.Icc (-T) T,
            (((t / (a ^ 2 + t ^ 2) : ℝ) : ℂ) * Complex.I) := by
          exact intervalIntegral.integral_add
            (scalarFourierLaplacePlemelj_zero_real_kernel_intervalIntegrable
              a ha T)
            (scalarFourierLaplacePlemelj_zero_odd_imaginary_intervalIntegrable
              a ha T)
    _ =
        (∫ t in Set.Icc (-T) T,
          ((-(a / (a ^ 2 + t ^ 2)) : ℝ) : ℂ)) + 0 := by
          exact congrArg
            (fun z : ℂ =>
              (∫ t in Set.Icc (-T) T,
                ((-(a / (a ^ 2 + t ^ 2)) : ℝ) : ℂ)) + z)
            (scalarFourierLaplacePlemelj_zero_odd_imaginary_integral_eq_zero
              a ha T)
    _ =
        ∫ t in Set.Icc (-T) T,
          ((-(a / (a ^ 2 + t ^ 2)) : ℝ) : ℂ) := by
          exact add_zero _
    _ =
        (-(2 : ℝ) * Real.arctan (T / a) : ℂ) := by
          exact
            scalarFourierLaplacePlemelj_zero_real_kernel_integral_eq_arctan
              a ha T

/-- Zero-time symmetric Cauchy window has the elementary arctangent value. -/
theorem scalarFourierLaplacePlemelj_zero_window_eq_arctan
    (a : ℝ) (ha : 0 < a) (T x : ℝ) (hx : x = 0) :
    (∫ t in Set.Icc (-T) T,
      (-1 / ((a : ℂ) + t * Complex.I)) *
        Complex.exp
          (Complex.I * (t : ℂ) * (x : ℂ))) *
        Complex.exp ((a : ℂ) * (x : ℂ)) =
      (-(2 : ℝ) * Real.arctan (T / a) : ℂ) := by
  have hinner :
      (∫ t in Set.Icc (-T) T,
        (-1 / ((a : ℂ) + t * Complex.I)) *
          Complex.exp
            (Complex.I * (t : ℂ) * (x : ℂ))) =
        ∫ t in Set.Icc (-T) T,
          (-1 / ((a : ℂ) + t * Complex.I)) := by
    exact intervalIntegral.integral_congr
      (Filter.Eventually.of_forall
        (fun t : ℝ =>
          congrArg
            (fun z : ℂ =>
              (-1 / ((a : ℂ) + t * Complex.I)) *
                Complex.exp z)
            (calc
              Complex.I * (t : ℂ) * (x : ℂ) =
                  Complex.I * (t : ℂ) * (0 : ℂ) := by
                exact congrArg
                  (fun y : ℂ => Complex.I * (t : ℂ) * y)
                  (congrArg (fun y : ℝ => (y : ℂ)) hx)
              _ = 0 := by
                exact mul_zero (Complex.I * (t : ℂ)))))
  have houter :
      Complex.exp ((a : ℂ) * (x : ℂ)) = 1 := by
    exact congrArg Complex.exp
      (calc
        (a : ℂ) * (x : ℂ) = (a : ℂ) * (0 : ℂ) := by
          exact congrArg
            (fun y : ℂ => (a : ℂ) * y)
            (congrArg (fun y : ℝ => (y : ℂ)) hx)
        _ = 0 := by
          exact mul_zero (a : ℂ))
  calc
    (∫ t in Set.Icc (-T) T,
        (-1 / ((a : ℂ) + t * Complex.I)) *
          Complex.exp
            (Complex.I * (t : ℂ) * (x : ℂ))) *
        Complex.exp ((a : ℂ) * (x : ℂ))
        =
        (∫ t in Set.Icc (-T) T,
          (-1 / ((a : ℂ) + t * Complex.I))) *
          Complex.exp ((a : ℂ) * (x : ℂ)) := by
          exact congrArg
            (fun z : ℂ => z * Complex.exp ((a : ℂ) * (x : ℂ)))
            hinner
    _ =
        (∫ t in Set.Icc (-T) T,
          (-1 / ((a : ℂ) + t * Complex.I))) * 1 := by
          exact congrArg
            (fun z : ℂ =>
              (∫ t in Set.Icc (-T) T,
                (-1 / ((a : ℂ) + t * Complex.I))) * z)
            houter
    _ =
        ∫ t in Set.Icc (-T) T,
          (-1 / ((a : ℂ) + t * Complex.I)) := by
          exact mul_one _
    _ =
        (-(2 : ℝ) * Real.arctan (T / a) : ℂ) := by
          exact scalarFourierLaplacePlemelj_zero_raw_window_eq_arctan
            a ha T

/-- The zero-time arctangent window is bounded by the scalar Plemelj constant. -/
theorem scalarFourierLaplacePlemelj_zero_arctan_bound
    (a : ℝ) (ha : 0 < a) (T : ℝ) :
    ‖((-(2 : ℝ) * Real.arctan (T / a) : ℝ) : ℂ)‖
      ≤ 2 * (Real.pi + 1) := by
  let y : ℝ := T / a
  let u : ℝ := Real.arctan y
  have hhalf_lt_pi : Real.pi / 2 < Real.pi :=
    half_lt_self Real.pi_pos
  have hupper : u ≤ Real.pi := by
    exact le_of_lt
      ((Real.arctan_lt_pi_div_two y).trans hhalf_lt_pi)
  have hneg_pi_lt_neg_half : -Real.pi < -(Real.pi / 2) :=
    neg_lt_neg hhalf_lt_pi
  have hlower : -Real.pi ≤ u := by
    exact le_of_lt
      (hneg_pi_lt_neg_half.trans
        (Real.neg_pi_div_two_lt_arctan y))
  have habs : |u| ≤ Real.pi :=
    abs_le.mpr ⟨hlower, hupper⟩
  have hnorm :
      ‖((-(2 : ℝ) * Real.arctan (T / a) : ℝ) : ℂ)‖ =
        |(-(2 : ℝ) * u)| := by
    unfold u
    unfold y
    exact RCLike.norm_ofReal (K := ℂ) (-(2 : ℝ) * Real.arctan (T / a))
  have habs_neg :
      |(-(2 : ℝ) * u)| = |(2 : ℝ) * u| := by
    have hneg_mul : (-(2 : ℝ) * u) = -((2 : ℝ) * u) :=
      neg_mul (2 : ℝ) u
    exact (congrArg abs hneg_mul).trans (abs_neg ((2 : ℝ) * u))
  have habs_mul :
      |(2 : ℝ) * u| = (2 : ℝ) * |u| := by
    calc
      |(2 : ℝ) * u| = |(2 : ℝ)| * |u| := by
        exact abs_mul (2 : ℝ) u
      _ = (2 : ℝ) * |u| := by
        exact congrArg (fun r : ℝ => r * |u|)
          (abs_of_nonneg zero_le_two)
  have htwo_abs_le : (2 : ℝ) * |u| ≤ 2 * Real.pi :=
    mul_le_mul_of_nonneg_left habs zero_le_two
  have hpi_le_pi_add_one : Real.pi ≤ Real.pi + 1 :=
    le_add_of_nonneg_right zero_le_one
  have htwo_pi_le : 2 * Real.pi ≤ 2 * (Real.pi + 1) :=
    mul_le_mul_of_nonneg_left hpi_le_pi_add_one zero_le_two
  exact
    (le_of_eq hnorm).trans
      ((le_of_eq habs_neg).trans
        ((le_of_eq habs_mul).trans
          (htwo_abs_le.trans htwo_pi_le)))

/-- Zero-time uniform finite-window bound for the normalized scalar Cauchy
kernel. -/
theorem scalarFourierLaplacePlemelj_unweighted_window_mul_exp_uniform_bound_zero
    (a : ℝ) (ha : 0 < a) (T x : ℝ) (hx : x = 0) :
    ‖(∫ t in Set.Icc (-T) T,
      (-1 / ((a : ℂ) + t * Complex.I)) *
        Complex.exp
          (Complex.I * (t : ℂ) * (x : ℂ))) *
        Complex.exp ((a : ℂ) * (x : ℂ))‖
      ≤ 2 * (Real.pi + 1) := by
  exact Eq.subst
    (motive := fun z : ℂ => ‖z‖ ≤ 2 * (Real.pi + 1))
    (scalarFourierLaplacePlemelj_zero_window_eq_arctan a ha T x hx)
    (scalarFourierLaplacePlemelj_zero_arctan_bound a ha T)

/-- Normalized scalar Fourier-Laplace Plemelj package.

For `a > 0`, the symmetric Fourier windows of
`-exp(a x)/(a + i t)` converge to the open half-line multiplier. -/
theorem scalarFourierLaplacePlemelj_openHalfLine
    (a : ℝ) (ha : 0 < a) :
    ∀ x : ℝ, x ≠ 0 →
      Tendsto
        (fun T : ℝ =>
          ∫ t in Set.Icc (-T) T,
            (-1 / ((a : ℂ) + t * Complex.I)) *
              Complex.exp
                (Complex.I * (t : ℂ) * (x : ℂ)) *
              Complex.exp ((a : ℂ) * (x : ℂ)))
        atTop
        (𝓝
          (Set.indicator (Set.Ioi (0 : ℝ))
            (fun _ : ℝ => (-2 * (Real.pi : ℂ))) x)) :=
  fun x hx0 =>
    scalarFourierLaplacePlemelj_pointwise_openHalfLine a ha x hx0

/-- The fixed-right-line scalar Cauchy window is the normalized
Fourier-Laplace Plemelj window with `a = c - 1`. -/
theorem fixedRightLine_scalarCauchyWindow_eq_normalizedLaplaceWindow
    (c : ℝ) (x T : ℝ) :
    (∫ t in Set.Icc (-T) T,
      (-1 / (((c : ℂ) + t * Complex.I) - 1)) *
        Complex.exp
          (Complex.I * (t : ℂ) * (x : ℂ)) *
        Complex.exp (((c - 1 : ℝ) : ℂ) * (x : ℂ))) =
    ∫ t in Set.Icc (-T) T,
      (-1 / (((c - 1 : ℝ) : ℂ) + t * Complex.I)) *
        Complex.exp
          (Complex.I * (t : ℂ) * (x : ℂ)) *
        Complex.exp (((c - 1 : ℝ) : ℂ) * (x : ℂ)) := by
  exact intervalIntegral.integral_congr
    (Filter.Eventually.of_forall
      (fun t : ℝ =>
        congrArg
          (fun z : ℂ =>
            (-1 / z) *
              Complex.exp
                (Complex.I * (t : ℂ) * (x : ℂ)) *
              Complex.exp (((c - 1 : ℝ) : ℂ) * (x : ℂ)))
          (calc
            ((c : ℂ) + t * Complex.I) - 1 =
                ((c : ℂ) - 1) + t * Complex.I := by
              exact sub_add_eq_add_sub (c : ℂ) (t * Complex.I) 1
            _ = (((c - 1 : ℝ) : ℂ) + t * Complex.I) := by
              exact congrArg (fun z : ℂ => z + t * Complex.I)
                (Complex.ofReal_sub c 1).symm)))

/-- Scalar fixed-right-line Cauchy/Plemelj package.

This is the one-dimensional analytic owner theorem behind the fixed-right-line
Cauchy projection: finite symmetric Cauchy windows converge pointwise to the
open-half-line multiplier. -/
theorem fixedRightLine_scalarCauchyWindow_plemelj_openHalfLine
    (c : ℝ) (hc : 1 < c) :
    ∀ x : ℝ, x ≠ 0 →
      Tendsto
        (fun T : ℝ =>
          ∫ t in Set.Icc (-T) T,
            (-1 / (((c : ℂ) + t * Complex.I) - 1)) *
              Complex.exp
                (Complex.I * (t : ℂ) * (x : ℂ)) *
              Complex.exp (((c - 1 : ℝ) : ℂ) * (x : ℂ)))
        atTop
        (𝓝
          (Set.indicator (Set.Ioi (0 : ℝ))
            (fun _ : ℝ => (-2 * (Real.pi : ℂ))) x)) := by
  have ha : 0 < c - 1 :=
    sub_pos.mpr hc
  have hbase :=
    scalarFourierLaplacePlemelj_openHalfLine
      (c - 1) ha
  intro x
  intro hx0
  have hfun :
      (fun T : ℝ =>
        ∫ t in Set.Icc (-T) T,
          (-1 / (((c : ℂ) + t * Complex.I) - 1)) *
            Complex.exp
              (Complex.I * (t : ℂ) * (x : ℂ)) *
            Complex.exp (((c - 1 : ℝ) : ℂ) * (x : ℂ))) =
      (fun T : ℝ =>
        ∫ t in Set.Icc (-T) T,
          (-1 / (((c - 1 : ℝ) : ℂ) + t * Complex.I)) *
            Complex.exp
              (Complex.I * (t : ℂ) * (x : ℂ)) *
            Complex.exp (((c - 1 : ℝ) : ℂ) * (x : ℂ))) := by
    funext T
    exact fixedRightLine_scalarCauchyWindow_eq_normalizedLaplaceWindow c x T
  exact Eq.subst
    (motive := fun u : ℝ → ℂ =>
      Tendsto u atTop
        (𝓝
          (Set.indicator (Set.Ioi (0 : ℝ))
            (fun _ : ℝ => (-2 * (Real.pi : ℂ))) x)))
    hfun.symm
    (hbase x hx0)

/-- Scalar fixed-right-line Plemelj theorem for finite symmetric Cauchy
windows, preserving the legacy theorem name while only asserting the
open-half-line pointwise limit. -/
theorem fixedRightLine_scalarCauchyWindow_plemelj_openHalfLine_with_uniform_bound
    (c : ℝ) (hc : 1 < c) (x : ℝ) (hx0 : x ≠ 0) :
    Tendsto
      (fun T : ℝ =>
        ∫ t in Set.Icc (-T) T,
          (-1 / (((c : ℂ) + t * Complex.I) - 1)) *
            Complex.exp
              (Complex.I * (t : ℂ) * (x : ℂ)) *
            Complex.exp (((c - 1 : ℝ) : ℂ) * (x : ℂ)))
      atTop
      (𝓝
        (Set.indicator (Set.Ioi (0 : ℝ))
          (fun _ : ℝ => (-2 * (Real.pi : ℂ))) x)) := by
  exact
    fixedRightLine_scalarCauchyWindow_plemelj_openHalfLine c hc x hx0

/-- Scalar fixed-right-line Plemelj theorem for finite symmetric Cauchy
windows, expressed as the open half-line multiplier. -/
theorem fixedRightLine_scalarCauchyWindow_pointwise_tendsto_openHalfLine
    (c : ℝ) (hc : 1 < c) (x : ℝ) (hx0 : x ≠ 0) :
    Tendsto
      (fun T : ℝ =>
        ∫ t in Set.Icc (-T) T,
          (-1 / (((c : ℂ) + t * Complex.I) - 1)) *
            Complex.exp
              (Complex.I * (t : ℂ) * (x : ℂ)) *
            Complex.exp (((c - 1 : ℝ) : ℂ) * (x : ℂ)))
      atTop
      (𝓝
        (Set.indicator (Set.Ioi (0 : ℝ))
          (fun _ : ℝ => (-2 * (Real.pi : ℂ))) x)) :=
  fixedRightLine_scalarCauchyWindow_plemelj_openHalfLine_with_uniform_bound
    c hc x hx0

/-- Pointwise positive-time Bromwich/Plemelj value for the fixed-right-line
finite scalar Cauchy windows. -/
theorem fixedRightLine_scalarCauchyWindow_pointwise_tendsto_positive
    (c : ℝ) (hc : 1 < c) (x : ℝ) (hx : 0 < x) :
    Tendsto
      (fun T : ℝ =>
        ∫ t in Set.Icc (-T) T,
          (-1 / (((c : ℂ) + t * Complex.I) - 1)) *
            Complex.exp
              (Complex.I * (t : ℂ) * (x : ℂ)) *
            Complex.exp (((c - 1 : ℝ) : ℂ) * (x : ℂ)))
      atTop
      (𝓝 (-2 * (Real.pi : ℂ))) := by
  have hbase :
      Tendsto
        (fun T : ℝ =>
          ∫ t in Set.Icc (-T) T,
            (-1 / (((c : ℂ) + t * Complex.I) - 1)) *
              Complex.exp
                (Complex.I * (t : ℂ) * (x : ℂ)) *
              Complex.exp (((c - 1 : ℝ) : ℂ) * (x : ℂ)))
        atTop
        (𝓝
          (Set.indicator (Set.Ioi (0 : ℝ))
            (fun _ : ℝ => (-2 * (Real.pi : ℂ))) x)) :=
    fixedRightLine_scalarCauchyWindow_pointwise_tendsto_openHalfLine c hc x
      (ne_of_gt hx)
  have hvalue :
      Set.indicator (Set.Ioi (0 : ℝ))
        (fun _ : ℝ => (-2 * (Real.pi : ℂ))) x =
        (-2 * (Real.pi : ℂ)) :=
    indicator_of_mem hx
      (fun _ : ℝ => (-2 * (Real.pi : ℂ)))
  exact hvalue ▸ hbase

/-- Pointwise negative-time Bromwich/Plemelj value for the fixed-right-line
finite scalar Cauchy windows. -/
theorem fixedRightLine_scalarCauchyWindow_pointwise_tendsto_negative
    (c : ℝ) (hc : 1 < c) (x : ℝ) (hx : x < 0) :
    Tendsto
      (fun T : ℝ =>
        ∫ t in Set.Icc (-T) T,
          (-1 / (((c : ℂ) + t * Complex.I) - 1)) *
            Complex.exp
              (Complex.I * (t : ℂ) * (x : ℂ)) *
            Complex.exp (((c - 1 : ℝ) : ℂ) * (x : ℂ)))
      atTop
      (𝓝 0) := by
  have hbase :
      Tendsto
        (fun T : ℝ =>
          ∫ t in Set.Icc (-T) T,
            (-1 / (((c : ℂ) + t * Complex.I) - 1)) *
              Complex.exp
                (Complex.I * (t : ℂ) * (x : ℂ)) *
              Complex.exp (((c - 1 : ℝ) : ℂ) * (x : ℂ)))
        atTop
        (𝓝
          (Set.indicator (Set.Ioi (0 : ℝ))
            (fun _ : ℝ => (-2 * (Real.pi : ℂ))) x)) :=
    fixedRightLine_scalarCauchyWindow_pointwise_tendsto_openHalfLine c hc x
      (ne_of_lt hx)
  have hnot : x ∉ Set.Ioi (0 : ℝ) :=
    fun hx_pos : 0 < x =>
      (not_lt_of_ge (le_of_lt hx)) hx_pos
  have hvalue :
      Set.indicator (Set.Ioi (0 : ℝ))
        (fun _ : ℝ => (-2 * (Real.pi : ℂ))) x = 0 :=
    indicator_of_not_mem hnot
      (fun _ : ℝ => (-2 * (Real.pi : ℂ)))
  exact hvalue ▸ hbase

/-- The positive upper-arc Jordan majorant remains bounded after multiplication
by the compensating exponential on compact intervals away from zero. -/
theorem scalarFourierLaplacePlemelj_positiveUpperArcJordanPrefactor_eventually_le
    (a : ℝ) :
    ∀ᶠ T in atTop,
      Real.pi * T / (T - a) ≤ Real.pi + 1 := by
  have hlimit :
      Tendsto
        (fun T : ℝ => Real.pi * T / (T - a))
        atTop
        (𝓝 Real.pi) :=
    scalarFourierLaplacePlemelj_positiveUpperArcJordanPrefactor_tendsto_pi a
  have hpi_lt : Real.pi < Real.pi + 1 :=
    lt_add_of_pos_right Real.pi zero_lt_one
  exact
    (hlimit (Set.Iio_mem_nhds hpi_lt)).mono
      (fun T hT => le_of_lt hT)

/-- Real exponential factor in the positive away-zero compact interval is
bounded by the endpoint exponential. -/
theorem scalarFourierLaplacePlemelj_positive_exp_norm_le_intervalEndpoint
    (a : ℝ) (ha : 0 < a) (R x : ℝ) (hxR : ‖x‖ ≤ R) :
    ‖Complex.exp ((a : ℂ) * (x : ℂ))‖ ≤ Real.exp (a * R) := by
  have hx_le_R : x ≤ R :=
    (le_abs_self x).trans hxR
  have hax_le_aR : a * x ≤ a * R :=
    mul_le_mul_of_nonneg_left hx_le_R ha.le
  have hnorm_eq :
      ‖Complex.exp ((a : ℂ) * (x : ℂ))‖ = Real.exp (a * x) := by
    calc
      ‖Complex.exp ((a : ℂ) * (x : ℂ))‖ =
          Complex.abs (Complex.exp ((a : ℂ) * (x : ℂ))) := by
        exact Complex.norm_eq_abs (Complex.exp ((a : ℂ) * (x : ℂ)))
      _ =
          Real.exp (((a : ℂ) * (x : ℂ)).re) := by
        exact Complex.abs_exp ((a : ℂ) * (x : ℂ))
      _ =
          Real.exp
            ((a : ℂ).re * (x : ℂ).re -
              (a : ℂ).im * (x : ℂ).im) := by
        exact congrArg Real.exp (Complex.mul_re (a : ℂ) (x : ℂ))
      _ =
          Real.exp (a * (x : ℂ).re -
              (a : ℂ).im * (x : ℂ).im) := by
        exact congrArg
          (fun r : ℝ =>
            Real.exp
              (r * (x : ℂ).re - (a : ℂ).im * (x : ℂ).im))
          (Complex.ofReal_re a)
      _ =
          Real.exp (a * x -
              (a : ℂ).im * (x : ℂ).im) := by
        exact congrArg
          (fun r : ℝ =>
            Real.exp (a * r - (a : ℂ).im * (x : ℂ).im))
          (Complex.ofReal_re x)
      _ =
          Real.exp (a * x - 0 * (x : ℂ).im) := by
        exact congrArg
          (fun r : ℝ => Real.exp (a * x - r * (x : ℂ).im))
          (Complex.ofReal_im a)
      _ =
          Real.exp (a * x - 0) := by
        exact congrArg Real.exp (congrArg (fun r : ℝ => a * x - r)
          (zero_mul (x : ℂ).im))
      _ =
          Real.exp (a * x) := by
        exact congrArg Real.exp (sub_zero (a * x))
  exact (le_of_eq hnorm_eq).trans (Real.exp_le_exp.mpr hax_le_aR)

/-- Reciprocal factor in the positive away-zero Jordan majorant is bounded by
the away-from-zero threshold. -/
theorem scalarFourierLaplacePlemelj_positive_awayZero_reciprocal_le
    (T x δ : ℝ) (hT : 0 < T) (hδ : 0 < δ) (hδx : δ ≤ x) :
    (T * x)⁻¹ ≤ (T * δ)⁻¹ := by
  have hTδ_pos : 0 < T * δ :=
    mul_pos hT hδ
  have hTδ_le_Tx : T * δ ≤ T * x :=
    mul_le_mul_of_nonneg_left hδx hT.le
  exact inv_anti₀ hTδ_pos hTδ_le_Tx

/-- Product assembly for the positive upper-arc Jordan majorant away from
zero. -/
theorem scalarFourierLaplacePlemelj_positiveUpperArcJordanMajorant_awayZero_mulExp_bound_eventually_of_factors
    (a : ℝ) (ha : 0 < a) (R δ B : ℝ) (hδ : 0 < δ)
    (hB_nonneg : 0 ≤ B)
    (hpref :
      ∀ᶠ T in atTop,
        Real.pi * T / (T - a) ≤ B) :
    ∃ C : ℝ,
      0 ≤ C ∧
        ∀ᶠ T in atTop,
          ∀ x : ℝ,
            δ ≤ x →
            ‖x‖ ≤ R →
              scalarFourierLaplacePlemelj_positiveUpperArcJordanMajorant a x T *
                ‖Complex.exp ((a : ℂ) * (x : ℂ))‖ ≤ C := by
  let C : ℝ := B * δ⁻¹ * Real.exp (a * R)
  have hδ_inv_nonneg : 0 ≤ δ⁻¹ :=
    inv_nonneg_of_nonneg hδ.le
  have hexp_nonneg : 0 ≤ Real.exp (a * R) :=
    (Real.exp_pos (a * R)).le
  have hC_nonneg : 0 ≤ C := by
    unfold C
    exact mul_nonneg (mul_nonneg hB_nonneg hδ_inv_nonneg) hexp_nonneg
  refine ⟨C, hC_nonneg, ?_⟩
  exact
    (hpref.and (eventually_gt_atTop (max a 1))).mono
      (fun T hTpair =>
        fun x hδx hxR =>
          let Pref : ℝ := Real.pi * T / (T - a)
          let Rec : ℝ := (T * x)⁻¹
          let E : ℝ := ‖Complex.exp ((a : ℂ) * (x : ℂ))‖
          have hpref_le : Pref ≤ B := hTpair.1
          have hmax : max a 1 < T := hTpair.2
          have haT : a < T := (le_max_left a 1).trans_lt hmax
          have h_one_lt_T : 1 < T := (le_max_right a 1).trans_lt hmax
          have hT_pos : 0 < T := zero_lt_one.trans h_one_lt_T
          have hden_pos : 0 < T - a := sub_pos.mpr haT
          have hpref_nonneg : 0 ≤ Pref := by
            unfold Pref
            exact div_nonneg
              (mul_nonneg Real.pi_nonneg hT_pos.le)
              hden_pos.le
          have hrec_le_Tδ :
              Rec ≤ (T * δ)⁻¹ := by
            unfold Rec
            exact
              scalarFourierLaplacePlemelj_positive_awayZero_reciprocal_le
                T x δ hT_pos hδ hδx
          have hδ_le_Tδ : δ ≤ T * δ := by
            calc
              δ = 1 * δ := by
                exact (one_mul δ).symm
              _ ≤ T * δ := by
                exact mul_le_mul_of_nonneg_right h_one_lt_T.le hδ.le
          have hTδ_inv_le : (T * δ)⁻¹ ≤ δ⁻¹ :=
            inv_anti₀ hδ hδ_le_Tδ
          have hrec_le : Rec ≤ δ⁻¹ :=
            hrec_le_Tδ.trans hTδ_inv_le
          have hrec_nonneg : 0 ≤ Rec := by
            unfold Rec
            exact inv_nonneg_of_nonneg (mul_nonneg hT_pos.le (hδ.le.trans hδx))
          have hE_le : E ≤ Real.exp (a * R) := by
            unfold E
            exact
              scalarFourierLaplacePlemelj_positive_exp_norm_le_intervalEndpoint
                a ha R x hxR
          have hE_nonneg : 0 ≤ E := by
            unfold E
            exact norm_nonneg _
          have h_pref_rec :
              Pref * Rec ≤ B * δ⁻¹ :=
            mul_le_mul hpref_le hrec_le hrec_nonneg hB_nonneg
          have h_product :
              (Pref * Rec) * E ≤ (B * δ⁻¹) * Real.exp (a * R) :=
            mul_le_mul h_pref_rec hE_le hE_nonneg
              (mul_nonneg hB_nonneg hδ_inv_nonneg)
          calc
            scalarFourierLaplacePlemelj_positiveUpperArcJordanMajorant a x T *
                ‖Complex.exp ((a : ℂ) * (x : ℂ))‖ =
                (Pref * Rec) * E := by
              rfl
            _ ≤ (B * δ⁻¹) * Real.exp (a * R) := h_product
            _ = C := by
              rfl)

theorem scalarFourierLaplacePlemelj_positiveUpperArcJordanMajorant_awayZero_mulExp_bound_eventually
    (a : ℝ) (ha : 0 < a) (R δ : ℝ) (hδ : 0 < δ) :
    ∃ C : ℝ,
      0 ≤ C ∧
        ∀ᶠ T in atTop,
          ∀ x : ℝ,
            δ ≤ x →
            ‖x‖ ≤ R →
              scalarFourierLaplacePlemelj_positiveUpperArcJordanMajorant a x T *
                ‖Complex.exp ((a : ℂ) * (x : ℂ))‖ ≤ C := by
  let B : ℝ := Real.pi + 1
  have hB_nonneg : 0 ≤ B := by
    unfold B
    exact add_nonneg Real.pi_nonneg zero_le_one
  exact
    scalarFourierLaplacePlemelj_positiveUpperArcJordanMajorant_awayZero_mulExp_bound_eventually_of_factors
      a ha R δ B hδ hB_nonneg
      (scalarFourierLaplacePlemelj_positiveUpperArcJordanPrefactor_eventually_le
        a)

/-- Positive upper-arc away-from-zero estimate from its Jordan majorant. -/
theorem scalarFourierLaplacePlemelj_positiveUpperArc_awayZero_mulExp_norm_bound_eventually_of_jordan
    (a : ℝ) (ha : 0 < a) (R δ Cj : ℝ) (hδ : 0 < δ)
    (hCj_nonneg : 0 ≤ Cj)
    (hjordan :
      ∀ᶠ T in atTop,
        ∀ x : ℝ,
          δ ≤ x →
          ‖x‖ ≤ R →
            scalarFourierLaplacePlemelj_positiveUpperArcJordanMajorant a x T *
              ‖Complex.exp ((a : ℂ) * (x : ℂ))‖ ≤ Cj) :
    ∃ C : ℝ,
      0 ≤ C ∧
        ∀ᶠ T in atTop,
          ∀ x : ℝ,
            δ ≤ x →
            ‖x‖ ≤ R →
              ‖scalarFourierLaplacePlemelj_positiveUpperArc a x T *
                Complex.exp ((a : ℂ) * (x : ℂ))‖ ≤ C := by
  exact
    ⟨Cj, hCj_nonneg,
      (hjordan.and (eventually_gt_atTop a)).mono
        (fun T hTpair =>
          fun x hδx hxR =>
            have hxpos : x ∈ Set.Ioi (0 : ℝ) :=
              hδ.trans_le hδx
            have harc :
                ‖scalarFourierLaplacePlemelj_positiveUpperArc a x T‖ ≤
                  scalarFourierLaplacePlemelj_positiveUpperArcJordanMajorant a x T :=
              (scalarFourierLaplacePlemelj_positiveUpperArc_norm_le_jordanDensity_integral
                a ha x hxpos T hTpair.2).trans
                (scalarFourierLaplacePlemelj_positiveUpperArcJordanDensity_integral_le_majorant
                  a ha x hxpos T hTpair.2)
            have hexp_nonneg :
                0 ≤ ‖Complex.exp ((a : ℂ) * (x : ℂ))‖ :=
              norm_nonneg _
            calc
              ‖scalarFourierLaplacePlemelj_positiveUpperArc a x T *
                  Complex.exp ((a : ℂ) * (x : ℂ))‖ =
                  ‖scalarFourierLaplacePlemelj_positiveUpperArc a x T‖ *
                    ‖Complex.exp ((a : ℂ) * (x : ℂ))‖ := by
                exact norm_mul
                  (scalarFourierLaplacePlemelj_positiveUpperArc a x T)
                  (Complex.exp ((a : ℂ) * (x : ℂ)))
              _ ≤
                  scalarFourierLaplacePlemelj_positiveUpperArcJordanMajorant a x T *
                    ‖Complex.exp ((a : ℂ) * (x : ℂ))‖ := by
                exact mul_le_mul_of_nonneg_right harc hexp_nonneg
              _ ≤ Cj := hTpair.1 x hδx hxR)⟩

theorem scalarFourierLaplacePlemelj_positiveUpperArc_awayZero_mulExp_norm_bound_eventually
    (a : ℝ) (ha : 0 < a) (R δ : ℝ) (hδ : 0 < δ) :
    ∃ C : ℝ,
      0 ≤ C ∧
        ∀ᶠ T in atTop,
          ∀ x : ℝ,
            δ ≤ x →
            ‖x‖ ≤ R →
              ‖scalarFourierLaplacePlemelj_positiveUpperArc a x T *
                Complex.exp ((a : ℂ) * (x : ℂ))‖ ≤ C := by
  match
    scalarFourierLaplacePlemelj_positiveUpperArcJordanMajorant_awayZero_mulExp_bound_eventually
      a ha R δ hδ
  with
  | ⟨Cj, hCj_nonneg, hjordan⟩ =>
      exact
        scalarFourierLaplacePlemelj_positiveUpperArc_awayZero_mulExp_norm_bound_eventually_of_jordan
          a ha R δ Cj hδ hCj_nonneg hjordan

/-- Radius-qualified finite upper-half-plane residue identity for the
positive-time scalar window. -/
theorem scalarFourierLaplacePlemelj_positive_window_add_upperArc_eq_residueValue_of_radius
    (a : ℝ) (ha : 0 < a) (x : ℝ) (hx : x ∈ Set.Ioi (0 : ℝ))
    (T : ℝ) (hT : a < T) :
      (∫ t in Set.Icc (-T) T,
        (-1 / ((a : ℂ) + t * Complex.I)) *
          Complex.exp
            (Complex.I * (t : ℂ) * (x : ℂ))) +
          scalarFourierLaplacePlemelj_positiveUpperArc a x T =
        (-2 * (Real.pi : ℂ)) *
          Complex.exp (-(a : ℂ) * (x : ℂ)) := by
  have hclosed :
      scalarFourierLaplacePlemelj_positiveClosedContour a x T =
        (-2 * (Real.pi : ℂ)) *
          Complex.exp (-(a : ℂ) * (x : ℂ)) :=
    scalarFourierLaplacePlemelj_positiveClosedContour_eq_residueValue_of_poleInside
      a ha x hx T hT
  exact
    (scalarFourierLaplacePlemelj_positiveClosedContour_eq_window_add_upperArc
      a x T).symm.trans hclosed

/-- After compensation by `exp (a x)`, the positive finite window and the
compensated upper arc add to the constant residue. -/
theorem scalarFourierLaplacePlemelj_positive_window_mul_exp_add_upperArc_mul_exp_eq_residue_of_radius
    (a : ℝ) (ha : 0 < a) (x : ℝ) (hx : x ∈ Set.Ioi (0 : ℝ))
    (T : ℝ) (hT : a < T) :
      ((∫ t in Set.Icc (-T) T,
        (-1 / ((a : ℂ) + t * Complex.I)) *
          Complex.exp
            (Complex.I * (t : ℂ) * (x : ℂ))) *
        Complex.exp ((a : ℂ) * (x : ℂ))) +
        scalarFourierLaplacePlemelj_positiveUpperArc a x T *
          Complex.exp ((a : ℂ) * (x : ℂ)) =
      (-2 * (Real.pi : ℂ)) := by
  let W : ℂ :=
    ∫ t in Set.Icc (-T) T,
      (-1 / ((a : ℂ) + t * Complex.I)) *
        Complex.exp
          (Complex.I * (t : ℂ) * (x : ℂ))
  let A : ℂ := scalarFourierLaplacePlemelj_positiveUpperArc a x T
  let E : ℂ := Complex.exp ((a : ℂ) * (x : ℂ))
  let R : ℂ := (-2 * (Real.pi : ℂ))
  have hraw :
      W + A =
        R * Complex.exp (-(a : ℂ) * (x : ℂ)) := by
    exact
      scalarFourierLaplacePlemelj_positive_window_add_upperArc_eq_residueValue_of_radius
        a ha x hx T hT
  have hmul :
      (W + A) * E =
        (R * Complex.exp (-(a : ℂ) * (x : ℂ))) * E := by
    exact congrArg (fun z : ℂ => z * E) hraw
  have hcollapse :
      (R * Complex.exp (-(a : ℂ) * (x : ℂ))) * E = R := by
    exact
      scalarFourierLaplacePlemelj_positive_laplaceJump_mul_eq_constant
        a x
  calc
    W * E + A * E = (W + A) * E := by
      exact (add_mul W A E).symm
    _ = (R * Complex.exp (-(a : ℂ) * (x : ℂ))) * E := hmul
    _ = R := hcollapse

/-- Exact radius-qualified positive finite-window formula after moving the
compensating exponential inside the window. -/
theorem scalarFourierLaplacePlemelj_positive_window_with_exp_eq_residue_sub_upperArc_mul_exp_of_radius
    (a : ℝ) (ha : 0 < a) (x : ℝ) (hx : x ∈ Set.Ioi (0 : ℝ))
    (T : ℝ) (hT : a < T) :
      (∫ t in Set.Icc (-T) T,
        (-1 / ((a : ℂ) + t * Complex.I)) *
          Complex.exp
            (Complex.I * (t : ℂ) * (x : ℂ)) *
          Complex.exp ((a : ℂ) * (x : ℂ))) =
      (-2 * (Real.pi : ℂ)) -
        scalarFourierLaplacePlemelj_positiveUpperArc a x T *
          Complex.exp ((a : ℂ) * (x : ℂ)) := by
  let W : ℂ :=
    ∫ t in Set.Icc (-T) T,
      (-1 / ((a : ℂ) + t * Complex.I)) *
        Complex.exp
          (Complex.I * (t : ℂ) * (x : ℂ))
  let A : ℂ := scalarFourierLaplacePlemelj_positiveUpperArc a x T
  let E : ℂ := Complex.exp ((a : ℂ) * (x : ℂ))
  let R : ℂ := (-2 * (Real.pi : ℂ))
  have hadd :
      W * E + A * E = R :=
    scalarFourierLaplacePlemelj_positive_window_mul_exp_add_upperArc_mul_exp_eq_residue_of_radius
      a ha x hx T hT
  have hsub :
      W * E = R - A * E := by
    calc
      W * E = (W * E + A * E) - A * E := by
        exact (add_sub_cancel_right (W * E) (A * E)).symm
      _ = R - A * E := by
        exact congrArg (fun z : ℂ => z - A * E) hadd
  have hwindow :
      W * E =
        ∫ t in Set.Icc (-T) T,
          (-1 / ((a : ℂ) + t * Complex.I)) *
            Complex.exp
              (Complex.I * (t : ℂ) * (x : ℂ)) *
            Complex.exp ((a : ℂ) * (x : ℂ)) :=
    scalarFourierLaplacePlemelj_positive_window_mul_exp_eq_window_with_exp
      a x T
  exact hwindow.symm.trans hsub

/-- Radius-qualified positive finite-window norm estimate from the compensated
upper-arc norm. -/
theorem scalarFourierLaplacePlemelj_positive_window_with_exp_norm_le_residue_add_upperArc_of_radius
    (a : ℝ) (ha : 0 < a) (x : ℝ) (hx : x ∈ Set.Ioi (0 : ℝ))
    (T : ℝ) (hT : a < T) :
      ‖(∫ t in Set.Icc (-T) T,
        (-1 / ((a : ℂ) + t * Complex.I)) *
          Complex.exp
            (Complex.I * (t : ℂ) * (x : ℂ)) *
          Complex.exp ((a : ℂ) * (x : ℂ)))‖
      ≤ ‖(-2 * (Real.pi : ℂ))‖ +
          ‖scalarFourierLaplacePlemelj_positiveUpperArc a x T *
            Complex.exp ((a : ℂ) * (x : ℂ))‖ := by
  let A : ℂ := scalarFourierLaplacePlemelj_positiveUpperArc a x T
  let E : ℂ := Complex.exp ((a : ℂ) * (x : ℂ))
  let R : ℂ := (-2 * (Real.pi : ℂ))
  let Wexp : ℂ :=
    ∫ t in Set.Icc (-T) T,
      (-1 / ((a : ℂ) + t * Complex.I)) *
        Complex.exp
          (Complex.I * (t : ℂ) * (x : ℂ)) *
        Complex.exp ((a : ℂ) * (x : ℂ))
  have heq :
      Wexp = R - A * E :=
    scalarFourierLaplacePlemelj_positive_window_with_exp_eq_residue_sub_upperArc_mul_exp_of_radius
      a ha x hx T hT
  calc
    ‖Wexp‖ = ‖R - A * E‖ := by
      exact congrArg norm heq
    _ ≤ ‖R‖ + ‖A * E‖ := by
      exact norm_sub_le R (A * E)

/-- Positive away-from-zero window bound from the upper-arc bound and the
positive residue identity. -/
theorem scalarFourierLaplacePlemelj_compactInterval_positive_awayZero_norm_bound_eventually_of_arc
    (a : ℝ) (ha : 0 < a) (R δ Carc : ℝ) (hδ : 0 < δ)
    (hCarc_nonneg : 0 ≤ Carc)
    (harc :
      ∀ᶠ T in atTop,
        ∀ x : ℝ,
          δ ≤ x →
          ‖x‖ ≤ R →
            ‖scalarFourierLaplacePlemelj_positiveUpperArc a x T *
              Complex.exp ((a : ℂ) * (x : ℂ))‖ ≤ Carc) :
    ∃ C : ℝ,
      0 ≤ C ∧
        ∀ᶠ T in atTop,
          ∀ x : ℝ,
            δ ≤ x →
            ‖x‖ ≤ R →
              ‖(∫ t in Set.Icc (-T) T,
                (-1 / ((a : ℂ) + t * Complex.I)) *
                  Complex.exp
                    (Complex.I * (t : ℂ) * (x : ℂ)) *
                  Complex.exp ((a : ℂ) * (x : ℂ)))‖
              ≤ C := by
  let Cresidue : ℝ := ‖(-2 * (Real.pi : ℂ))‖
  let C : ℝ := Cresidue + Carc
  have hCresidue_nonneg : 0 ≤ Cresidue := by
    unfold Cresidue
    exact norm_nonneg _
  have hC_nonneg : 0 ≤ C := by
    unfold C
    exact add_nonneg hCresidue_nonneg hCarc_nonneg
  have hresidue_norm :
      ‖(-2 * (Real.pi : ℂ))‖ = Cresidue := by
    rfl
  exact
    ⟨C, hC_nonneg,
      (harc.and (eventually_gt_atTop a)).mono
        (fun T hTpair x hδx hxR =>
          have hxpos : x ∈ Set.Ioi (0 : ℝ) :=
            lt_of_lt_of_le hδ hδx
          have hwindow :
              ‖(∫ t in Set.Icc (-T) T,
                (-1 / ((a : ℂ) + t * Complex.I)) *
                  Complex.exp
                    (Complex.I * (t : ℂ) * (x : ℂ)) *
                  Complex.exp ((a : ℂ) * (x : ℂ)))‖
              ≤ ‖(-2 * (Real.pi : ℂ))‖ +
                  ‖scalarFourierLaplacePlemelj_positiveUpperArc a x T *
                    Complex.exp ((a : ℂ) * (x : ℂ))‖ :=
            scalarFourierLaplacePlemelj_positive_window_with_exp_norm_le_residue_add_upperArc_of_radius
              a ha x hxpos T hTpair.2
          calc
            ‖(∫ t in Set.Icc (-T) T,
              (-1 / ((a : ℂ) + t * Complex.I)) *
                Complex.exp
                  (Complex.I * (t : ℂ) * (x : ℂ)) *
                Complex.exp ((a : ℂ) * (x : ℂ)))‖
                ≤ ‖(-2 * (Real.pi : ℂ))‖ +
                    ‖scalarFourierLaplacePlemelj_positiveUpperArc a x T *
                      Complex.exp ((a : ℂ) * (x : ℂ))‖ := hwindow
            _ ≤ ‖(-2 * (Real.pi : ℂ))‖ + Carc := by
                exact add_le_add_left (hTpair.1 x hδx hxR)
                  ‖(-2 * (Real.pi : ℂ))‖
            _ = C := by
                exact congrArg (fun r : ℝ => r + Carc) hresidue_norm)⟩

theorem scalarFourierLaplacePlemelj_compactInterval_positive_awayZero_norm_bound_eventually
    (a : ℝ) (ha : 0 < a) (R δ : ℝ) (hδ : 0 < δ) :
    ∃ C : ℝ,
      0 ≤ C ∧
        ∀ᶠ T in atTop,
          ∀ x : ℝ,
            δ ≤ x →
            ‖x‖ ≤ R →
              ‖(∫ t in Set.Icc (-T) T,
                (-1 / ((a : ℂ) + t * Complex.I)) *
                  Complex.exp
                    (Complex.I * (t : ℂ) * (x : ℂ)) *
                  Complex.exp ((a : ℂ) * (x : ℂ)))‖
              ≤ C := by
  match scalarFourierLaplacePlemelj_positiveUpperArc_awayZero_mulExp_norm_bound_eventually
    a ha R δ hδ with
  | ⟨Carc, hCarc_nonneg, harc⟩ =>
      exact
        scalarFourierLaplacePlemelj_compactInterval_positive_awayZero_norm_bound_eventually_of_arc
          a ha R δ Carc hδ hCarc_nonneg harc

/-- Even-cosine real part of the uncompensated Cauchy Fourier window. -/
noncomputable def scalarFourierLaplacePlemelj_uncompensated_evenCosineWindow
    (a T x : ℝ) : ℝ :=
  ∫ t in Set.Icc (-T) T,
    (-(a / (a ^ 2 + t ^ 2))) * Real.cos (t * x)

/-- Odd-sine real contribution of the uncompensated Cauchy Fourier window. -/
noncomputable def scalarFourierLaplacePlemelj_uncompensated_oddSineWindow
    (a T x : ℝ) : ℝ :=
  ∫ t in Set.Icc (-T) T,
    (t / (a ^ 2 + t ^ 2)) * Real.sin (t * x)

/-- Pointwise domination of the even-cosine integrand by the positive Cauchy
kernel. -/
theorem scalarFourierLaplacePlemelj_uncompensated_evenCosine_integrand_abs_le_kernel
    (a : ℝ) (ha : 0 < a) (t x : ℝ) :
    |(-(a / (a ^ 2 + t ^ 2))) * Real.cos (t * x)| ≤
      a / (a ^ 2 + t ^ 2) := by
  let p : ℝ := a / (a ^ 2 + t ^ 2)
  let c : ℝ := Real.cos (t * x)
  have hden_pos : 0 < a ^ 2 + t ^ 2 :=
    scalarFourierLaplacePlemelj_zero_denominator_pos a ha t
  have hp_nonneg : 0 ≤ p := by
    unfold p
    exact div_nonneg ha.le hden_pos.le
  have hc_abs : |c| ≤ 1 := by
    unfold c
    exact abs_cos_le_one (t * x)
  have habs :
      |(-p) * c| = p * |c| := by
    calc
      |(-p) * c| = |-p| * |c| := by
        exact abs_mul (-p) c
      _ = |p| * |c| := by
        exact congrArg (fun r : ℝ => r * |c|) (abs_neg p)
      _ = p * |c| := by
        exact congrArg (fun r : ℝ => r * |c|) (abs_of_nonneg hp_nonneg)
  have hmul : p * |c| ≤ p * 1 :=
    mul_le_mul_of_nonneg_left hc_abs hp_nonneg
  calc
    |(-(a / (a ^ 2 + t ^ 2))) * Real.cos (t * x)|
        = |(-p) * c| := by
          unfold p
          unfold c
          rfl
    _ = p * |c| := habs
    _ ≤ p * 1 := hmul
    _ = a / (a ^ 2 + t ^ 2) := by
          unfold p
          exact mul_one (a / (a ^ 2 + t ^ 2))

/-- Interval integrability of the positive Cauchy kernel on symmetric finite
windows. -/
theorem scalarFourierLaplacePlemelj_uncompensated_positiveKernel_intervalIntegrable
    (a : ℝ) (ha : 0 < a) (T : ℝ) :
    IntervalIntegrable
      (fun t : ℝ => a / (a ^ 2 + t ^ 2))
      volume (-T) T := by
  have hden_cont : Continuous (fun t : ℝ => a ^ 2 + t ^ 2) :=
    continuous_const.add (continuous_id.pow 2)
  have hden_ne : ∀ t : ℝ, a ^ 2 + t ^ 2 ≠ 0 :=
    scalarFourierLaplacePlemelj_zero_denominator_ne_zero a ha
  have hquot_cont : Continuous (fun t : ℝ => a / (a ^ 2 + t ^ 2)) :=
    continuous_const.div hden_cont hden_ne
  exact hquot_cont.intervalIntegrable (-T) T

/-- Interval majorization of the even-cosine window by the positive Cauchy
kernel mass. -/
theorem scalarFourierLaplacePlemelj_uncompensated_evenCosineWindow_abs_le_kernelMass_of_pointwise
    (a : ℝ) (ha : 0 < a) (T x : ℝ)
    (hpoint :
      ∀ t : ℝ,
        |(-(a / (a ^ 2 + t ^ 2))) * Real.cos (t * x)| ≤
          a / (a ^ 2 + t ^ 2)) :
    |scalarFourierLaplacePlemelj_uncompensated_evenCosineWindow a T x| ≤
      |∫ t in Set.Icc (-T) T, (a / (a ^ 2 + t ^ 2) : ℝ)| := by
  let f : ℝ → ℝ :=
    fun t : ℝ => (-(a / (a ^ 2 + t ^ 2))) * Real.cos (t * x)
  let g : ℝ → ℝ :=
    fun t : ℝ => a / (a ^ 2 + t ^ 2)
  have hmajor :
      ∀ᵐ t ∂volume.restrict (Ι (-T) T), ‖f t‖ ≤ g t :=
    Filter.Eventually.of_forall
      (fun t : ℝ => by
        calc
          ‖f t‖ = |f t| := by
            exact Real.norm_eq_abs (f t)
          _ =
              |(-(a / (a ^ 2 + t ^ 2))) * Real.cos (t * x)| := by
                unfold f
                rfl
          _ ≤ a / (a ^ 2 + t ^ 2) := hpoint t
          _ = g t := by
                unfold g
                rfl)
  have hg :
      IntervalIntegrable g volume (-T) T := by
    unfold g
    exact
      scalarFourierLaplacePlemelj_uncompensated_positiveKernel_intervalIntegrable
        a ha T
  have hbound :
      ‖∫ t in (-T)..T, f t‖ ≤
        |∫ t in (-T)..T, g t| :=
    intervalIntegral.norm_integral_le_of_norm_le
      (a := -T) (b := T) (μ := volume) (f := f) (g := g)
      hmajor hg
  calc
    |scalarFourierLaplacePlemelj_uncompensated_evenCosineWindow a T x|
        = ‖∫ t in (-T)..T, f t‖ := by
          unfold scalarFourierLaplacePlemelj_uncompensated_evenCosineWindow
          unfold f
          exact (Real.norm_eq_abs
            (∫ t in (-T)..T,
              (-(a / (a ^ 2 + t ^ 2))) * Real.cos (t * x))).symm
    _ ≤ |∫ t in (-T)..T, g t| := hbound
    _ =
        |∫ t in Set.Icc (-T) T, (a / (a ^ 2 + t ^ 2) : ℝ)| := by
          unfold g
          rfl

/-- Absolute integral majorization of the even-cosine component by the
nonoscillatory Cauchy kernel mass. -/
theorem scalarFourierLaplacePlemelj_uncompensated_evenCosineWindow_abs_le_kernelMass
    (a : ℝ) (ha : 0 < a) (T x : ℝ) :
    |scalarFourierLaplacePlemelj_uncompensated_evenCosineWindow a T x| ≤
      |∫ t in Set.Icc (-T) T, (a / (a ^ 2 + t ^ 2) : ℝ)| := by
  exact
    scalarFourierLaplacePlemelj_uncompensated_evenCosineWindow_abs_le_kernelMass_of_pointwise
      a ha T x
      (fun t : ℝ =>
        scalarFourierLaplacePlemelj_uncompensated_evenCosine_integrand_abs_le_kernel
          a ha t x)

/-- Exact arctangent primitive for the positive Cauchy kernel mass. -/
theorem scalarFourierLaplacePlemelj_uncompensated_kernelMass_eq_two_arctan
    (a : ℝ) (ha : 0 < a) (T : ℝ) :
    (∫ t in Set.Icc (-T) T, (a / (a ^ 2 + t ^ 2) : ℝ)) =
      (2 : ℝ) * Real.arctan (T / a) := by
  let P : ℝ → ℝ := fun t : ℝ => a / (a ^ 2 + t ^ 2)
  let A : ℝ := (2 : ℝ) * Real.arctan (T / a)
  have hneg_complex :
      (∫ t in Set.Icc (-T) T, ((-P t : ℝ) : ℂ)) =
        ((-A : ℝ) : ℂ) := by
    calc
      (∫ t in Set.Icc (-T) T, ((-P t : ℝ) : ℂ))
          =
          ∫ t in Set.Icc (-T) T,
            ((-(a / (a ^ 2 + t ^ 2)) : ℝ) : ℂ) := by
            exact intervalIntegral.integral_congr
              (Filter.Eventually.of_forall
                (fun t : ℝ => by
                  unfold P
                  rfl))
      _ =
          (-(2 : ℝ) * Real.arctan (T / a) : ℂ) := by
            exact
              scalarFourierLaplacePlemelj_zero_real_kernel_integral_eq_arctan
                a ha T
      _ = ((-A : ℝ) : ℂ) := by
            unfold A
            exact congrArg (fun r : ℝ => (r : ℂ))
              (neg_mul (2 : ℝ) (Real.arctan (T / a))).symm
  have hneg_real :
      (∫ t in Set.Icc (-T) T, (-P t : ℝ)) = -A := by
    have hofReal :
        (∫ t in Set.Icc (-T) T, ((-P t : ℝ) : ℂ)) =
          (((∫ t in Set.Icc (-T) T, (-P t : ℝ)) : ℝ) : ℂ) := by
      calc
        (∫ t in Set.Icc (-T) T, ((-P t : ℝ) : ℂ))
            =
            ∫ t in (-T)..T, ((-P t : ℝ) : ℂ) := by
              rfl
        _ =
            (((∫ t in (-T)..T, (-P t : ℝ)) : ℝ) : ℂ) := by
              exact intervalIntegral.integral_ofReal
        _ =
            (((∫ t in Set.Icc (-T) T, (-P t : ℝ)) : ℝ) : ℂ) := by
              rfl
    exact Complex.ofReal_injective (hofReal.symm.trans hneg_complex)
  have hneg_relation :
      (∫ t in Set.Icc (-T) T, (-P t : ℝ)) =
        -(∫ t in Set.Icc (-T) T, P t) := by
    calc
      (∫ t in Set.Icc (-T) T, (-P t : ℝ))
          =
          ∫ t in (-T)..T, (-P t : ℝ) := by
            rfl
      _ =
          -(∫ t in (-T)..T, P t) := by
            exact intervalIntegral.integral_neg
      _ =
          -(∫ t in Set.Icc (-T) T, P t) := by
            rfl
  have hneg_target :
      -(∫ t in Set.Icc (-T) T, P t) = -A :=
    hneg_relation.symm.trans hneg_real
  have htarget :
      (∫ t in Set.Icc (-T) T, P t) = A :=
    neg_injective hneg_target
  exact htarget

/-- Elementary arctangent bound for the positive Cauchy kernel primitive. -/
theorem scalarFourierLaplacePlemelj_two_mul_arctan_abs_le_pi
    (y : ℝ) :
    |(2 : ℝ) * Real.arctan y| ≤ Real.pi := by
  let u : ℝ := Real.arctan y
  have hupper_half : u < Real.pi / 2 := by
    unfold u
    exact Real.arctan_lt_pi_div_two y
  have hlower_half : -(Real.pi / 2) < u := by
    unfold u
    exact Real.neg_pi_div_two_lt_arctan y
  have htwo_pos : (0 : ℝ) < 2 :=
    two_pos
  have hmul_upper :
      (2 : ℝ) * u < 2 * (Real.pi / 2) :=
    mul_lt_mul_of_pos_left hupper_half htwo_pos
  have hmul_lower :
      2 * (-(Real.pi / 2)) < (2 : ℝ) * u :=
    mul_lt_mul_of_pos_left hlower_half htwo_pos
  have htwo_half : (2 : ℝ) * (Real.pi / 2) = Real.pi :=
    two_mul_div_two Real.pi
  have htwo_neg_half : (2 : ℝ) * (-(Real.pi / 2)) = -Real.pi := by
    calc
      (2 : ℝ) * (-(Real.pi / 2)) = -((2 : ℝ) * (Real.pi / 2)) := by
        exact mul_neg (2 : ℝ) (Real.pi / 2)
      _ = -Real.pi := by
        exact congrArg Neg.neg htwo_half
  have hupper : (2 : ℝ) * u ≤ Real.pi :=
    le_of_lt (hmul_upper.trans_eq htwo_half)
  have hlower : -Real.pi ≤ (2 : ℝ) * u :=
    le_of_lt (htwo_neg_half.symm.trans_lt hmul_lower)
  exact abs_le.mpr ⟨hlower, hupper⟩

/-- The symmetric nonoscillatory Cauchy kernel mass is bounded by `π`. -/
theorem scalarFourierLaplacePlemelj_uncompensated_kernelMass_abs_le_pi
    (a : ℝ) (ha : 0 < a) (T : ℝ) :
    |∫ t in Set.Icc (-T) T, (a / (a ^ 2 + t ^ 2) : ℝ)| ≤ Real.pi := by
  calc
    |∫ t in Set.Icc (-T) T, (a / (a ^ 2 + t ^ 2) : ℝ)|
        = |(2 : ℝ) * Real.arctan (T / a)| := by
          exact congrArg abs
            (scalarFourierLaplacePlemelj_uncompensated_kernelMass_eq_two_arctan
              a ha T)
    _ ≤ Real.pi :=
          scalarFourierLaplacePlemelj_two_mul_arctan_abs_le_pi (T / a)

/-- Fixed-constant Dirichlet bound for the even-cosine component of the
uncompensated Cauchy kernel. -/
theorem scalarFourierLaplacePlemelj_uncompensated_evenCosineWindow_abs_le_pi
    (a : ℝ) (ha : 0 < a) (T x : ℝ) :
    |scalarFourierLaplacePlemelj_uncompensated_evenCosineWindow a T x| ≤
      Real.pi := by
  exact
    (scalarFourierLaplacePlemelj_uncompensated_evenCosineWindow_abs_le_kernelMass
      a ha T x).trans
      (scalarFourierLaplacePlemelj_uncompensated_kernelMass_abs_le_pi
        a ha T)

/-- Uniform Dirichlet bound for the even-cosine part of the uncompensated
Cauchy Fourier window. -/
theorem scalarFourierLaplacePlemelj_uncompensated_evenCosineWindow_uniform_bound
    (a : ℝ) (ha : 0 < a) :
    ∃ C : ℝ,
      0 ≤ C ∧
        ∀ T x : ℝ,
          |scalarFourierLaplacePlemelj_uncompensated_evenCosineWindow a T x| ≤ C := by
  exact ⟨Real.pi, Real.pi_pos.le,
    fun T x =>
      scalarFourierLaplacePlemelj_uncompensated_evenCosineWindow_abs_le_pi
        a ha T x⟩

/-- Nonnegative-radius, positive-frequency normalized half-window Hilbert-sine
Dirichlet bound. -/
theorem scalarFourierLaplacePlemelj_dampedSineIntegral_smallPrefix_scaled_eq
    (A b : ℝ) (hA : 0 ≤ A) (hb : 0 < b) :
    (∫ v in (0)..A,
      (v / (b ^ 2 + v ^ 2)) * Real.sin v) =
      ∫ w in (0)..(A / b),
        (w / (1 + w ^ 2)) * Real.sin (b * w) := by
  let F : ℝ → ℝ :=
    fun v : ℝ => (v / (b ^ 2 + v ^ 2)) * Real.sin v
  have hb_ne : b ≠ 0 :=
    ne_of_gt hb
  have hend : (A / b) * b = A :=
    div_mul_cancel₀ A hb_ne
  have hpoint :
      ∀ w : ℝ,
        b * F (w * b) =
          (w / (1 + w ^ 2)) * Real.sin (b * w) := by
    intro w
    have hcoeff :
        b * ((w * b) / (b ^ 2 + (w * b) ^ 2)) =
          w / (1 + w ^ 2) :=
      scalarFourierLaplacePlemelj_scaledHilbertSineKernel_coefficient_identity
        b hb w
    have hphase : Real.sin (w * b) = Real.sin (b * w) :=
      congrArg Real.sin (mul_comm w b)
    calc
      b * F (w * b)
          =
          b *
            (((w * b) / (b ^ 2 + (w * b) ^ 2)) *
              Real.sin (w * b)) := by
            unfold F
            rfl
      _ =
          (b * ((w * b) / (b ^ 2 + (w * b) ^ 2))) *
            Real.sin (w * b) := by
            exact mul_assoc b
              ((w * b) / (b ^ 2 + (w * b) ^ 2))
              (Real.sin (w * b))
      _ =
          (w / (1 + w ^ 2)) * Real.sin (w * b) := by
            exact congrArg
              (fun r : ℝ => r * Real.sin (w * b))
              hcoeff
      _ =
          (w / (1 + w ^ 2)) * Real.sin (b * w) := by
            exact congrArg
              (fun s : ℝ => (w / (1 + w ^ 2)) * s)
              hphase
  have hsubst :
      b * ∫ w in (0)..(A / b), F (w * b) =
        ∫ v in (0 * b)..((A / b) * b), F v :=
    intervalIntegral.smul_integral_comp_mul_right
      (f := F) (a := 0) (b := A / b) b
  have hconst :
      b * ∫ w in (0)..(A / b), F (w * b) =
        ∫ w in (0)..(A / b),
          (w / (1 + w ^ 2)) * Real.sin (b * w) := by
    calc
      b * ∫ w in (0)..(A / b), F (w * b)
          =
          ∫ w in (0)..(A / b), b * F (w * b) := by
            exact (intervalIntegral.integral_const_mul
              (a := 0) (b := A / b) (μ := volume)
              b
              (fun w : ℝ => F (w * b))).symm
      _ =
          ∫ w in (0)..(A / b),
            (w / (1 + w ^ 2)) * Real.sin (b * w) := by
            exact intervalIntegral.integral_congr
              (Filter.Eventually.of_forall hpoint)
  calc
    (∫ v in (0)..A,
      (v / (b ^ 2 + v ^ 2)) * Real.sin v)
        = ∫ v in (0)..A, F v := by
          unfold F
          rfl
    _ = ∫ v in (0 * b)..((A / b) * b), F v := by
          exact congrArg₂
            (fun l r : ℝ => ∫ v in l..r, F v)
            (zero_mul b).symm
            hend.symm
    _ = b * ∫ w in (0)..(A / b), F (w * b) := by
          exact hsubst.symm
    _ =
        ∫ w in (0)..(A / b),
          (w / (1 + w ^ 2)) * Real.sin (b * w) := hconst

theorem scalarFourierLaplacePlemelj_scaledSmallPrefix_abs_le_one
    (R b : ℝ) (hR_nonneg : 0 ≤ R) (hR_le_one : R ≤ 1) :
    |∫ w in (0)..R,
      (w / (1 + w ^ 2)) * Real.sin (b * w)| ≤ 1 := by
  let f : ℝ → ℝ :=
    fun w : ℝ => (w / (1 + w ^ 2)) * Real.sin (b * w)
  have hpoint : ∀ w ∈ Ι (0 : ℝ) R, ‖f w‖ ≤ (1 : ℝ) := by
    intro w hw
    have hw_nonneg : 0 ≤ w :=
      (mem_uIcc.mp hw).1
    have hw_le_R : w ≤ R :=
      (mem_uIcc.mp hw).2
    have hw_le_one : w ≤ 1 :=
      hw_le_R.trans hR_le_one
    have hden_pos : 0 < 1 + w ^ 2 :=
      add_pos_of_pos_of_nonneg zero_lt_one (sq_nonneg w)
    have hcoeff_nonneg : 0 ≤ w / (1 + w ^ 2) :=
      div_nonneg hw_nonneg hden_pos.le
    have hcoeff_le_one : w / (1 + w ^ 2) ≤ 1 := by
      exact (div_le_one hden_pos).mpr
        (hw_le_one.trans
          (le_add_of_nonneg_right (sq_nonneg w)))
    have hsin_abs : |Real.sin (b * w)| ≤ 1 :=
      abs_le.mpr ⟨neg_one_le_sin (b * w), sin_le_one (b * w)⟩
    have habs :
        |f w| ≤ 1 := by
      calc
        |f w| =
            |w / (1 + w ^ 2)| * |Real.sin (b * w)| := by
            unfold f
            exact abs_mul (w / (1 + w ^ 2)) (Real.sin (b * w))
        _ =
            (w / (1 + w ^ 2)) * |Real.sin (b * w)| := by
            exact congrArg
              (fun r : ℝ => r * |Real.sin (b * w)|)
              (abs_of_nonneg hcoeff_nonneg)
        _ ≤ (w / (1 + w ^ 2)) * 1 := by
            exact mul_le_mul_of_nonneg_left hsin_abs hcoeff_nonneg
        _ = w / (1 + w ^ 2) := by
            exact mul_one (w / (1 + w ^ 2))
        _ ≤ 1 := hcoeff_le_one
    calc
      ‖f w‖ = |f w| := by
        exact Real.norm_eq_abs (f w)
      _ ≤ 1 := habs
  have hnorm :
      ‖∫ w in (0)..R, f w‖ ≤ (1 : ℝ) * |R - 0| :=
    intervalIntegral.norm_integral_le_of_norm_le_const hpoint
  have hlength : |R - 0| ≤ 1 := by
    calc
      |R - 0| = |R| := by
        exact congrArg abs (sub_zero R)
      _ = R := by
        exact abs_of_nonneg hR_nonneg
      _ ≤ 1 := hR_le_one
  have htarget :
      ‖∫ w in (0)..R, f w‖ ≤ 1 := by
    calc
      ‖∫ w in (0)..R, f w‖ ≤ (1 : ℝ) * |R - 0| := hnorm
      _ = |R - 0| := by
        exact one_mul |R - 0|
      _ ≤ 1 := hlength
  calc
    |∫ w in (0)..R,
      (w / (1 + w ^ 2)) * Real.sin (b * w)|
        = ‖∫ w in (0)..R, f w‖ := by
          unfold f
          exact (Real.norm_eq_abs
            (∫ w in (0)..R,
              (w / (1 + w ^ 2)) * Real.sin (b * w))).symm
    _ ≤ 1 := htarget

theorem scalarFourierLaplacePlemelj_dampedSineIntegral_smallPrefix_abs_le_one
    (A b : ℝ) (hA : 0 ≤ A) (hA_le_b : A ≤ b) (hb : 0 < b) :
    |∫ v in (0)..A,
      (v / (b ^ 2 + v ^ 2)) * Real.sin v| ≤ 1 := by
  have hb_nonneg : 0 ≤ b :=
    hb.le
  have hb_ne : b ≠ 0 :=
    ne_of_gt hb
  have hR_nonneg : 0 ≤ A / b :=
    div_nonneg hA hb_nonneg
  have hR_le_one : A / b ≤ 1 := by
    exact (div_le_one hb).mpr hA_le_b
  have hscale :
      (∫ v in (0)..A,
        (v / (b ^ 2 + v ^ 2)) * Real.sin v) =
        ∫ w in (0)..(A / b),
          (w / (1 + w ^ 2)) * Real.sin (b * w) :=
    scalarFourierLaplacePlemelj_dampedSineIntegral_smallPrefix_scaled_eq
      A b hA hb
  calc
    |∫ v in (0)..A,
      (v / (b ^ 2 + v ^ 2)) * Real.sin v|
        =
        |∫ w in (0)..(A / b),
          (w / (1 + w ^ 2)) * Real.sin (b * w)| := by
          exact congrArg abs hscale
    _ ≤ 1 :=
        scalarFourierLaplacePlemelj_scaledSmallPrefix_abs_le_one
          (A / b) b hR_nonneg hR_le_one

theorem scalarFourierLaplacePlemelj_one_le_two_pi :
    (1 : ℝ) ≤ (2 : ℝ) * Real.pi := by
  have hone_le_pi_half : (1 : ℝ) ≤ Real.pi / 2 :=
    Real.one_le_pi_div_two
  have hpi_half_le_pi : Real.pi / 2 ≤ Real.pi :=
    div_le_self Real.pi_pos.le one_le_two
  have hpi_le_two_pi : Real.pi ≤ (2 : ℝ) * Real.pi := by
    calc
      Real.pi = (1 : ℝ) * Real.pi := by
        exact (one_mul Real.pi).symm
      _ ≤ (2 : ℝ) * Real.pi := by
        exact mul_le_mul_of_nonneg_right one_le_two Real.pi_pos.le
  exact hone_le_pi_half.trans (hpi_half_le_pi.trans hpi_le_two_pi)

theorem scalarFourierLaplacePlemelj_two_le_two_pi :
    (2 : ℝ) ≤ (2 : ℝ) * Real.pi := by
  have hone_le_pi_half : (1 : ℝ) ≤ Real.pi / 2 :=
    Real.one_le_pi_div_two
  have htwo_pos : (0 : ℝ) < 2 :=
    two_pos
  have htwo_le_pi : (2 : ℝ) ≤ Real.pi := by
    have hone_mul_two_le_pi : (1 : ℝ) * 2 ≤ Real.pi :=
      (le_div_iff₀ htwo_pos).mp hone_le_pi_half
    calc
      (2 : ℝ) = (1 : ℝ) * 2 := by
        exact (one_mul 2).symm
      _ ≤ Real.pi := hone_mul_two_le_pi
  have hpi_le_two_pi : Real.pi ≤ (2 : ℝ) * Real.pi := by
    calc
      Real.pi = (1 : ℝ) * Real.pi := by
        exact (one_mul Real.pi).symm
      _ ≤ (2 : ℝ) * Real.pi := by
        exact mul_le_mul_of_nonneg_right one_le_two Real.pi_pos.le
  exact htwo_le_pi.trans hpi_le_two_pi

theorem scalarFourierLaplacePlemelj_dampedSineIntegral_tail_low_abs_le_one
    (A b : ℝ) (hb : 0 < b) (hbA : b ≤ A) (hA_le_one : A ≤ 1) :
    |∫ v in (b)..A,
      (v / (b ^ 2 + v ^ 2)) * Real.sin v| ≤ 1 := by
  let f : ℝ → ℝ :=
    fun v : ℝ => (v / (b ^ 2 + v ^ 2)) * Real.sin v
  have hpoint : ∀ v ∈ Ι b A, ‖f v‖ ≤ (1 : ℝ) := by
    intro v hv
    have hb_le_v : b ≤ v :=
      (mem_uIcc.mp hv).1
    have hv_le_A : v ≤ A :=
      (mem_uIcc.mp hv).2
    have hv_nonneg : 0 ≤ v :=
      hb.le.trans hb_le_v
    have hden_pos : 0 < b ^ 2 + v ^ 2 :=
      scalarFourierLaplacePlemelj_zero_denominator_pos b hb v
    have hcoeff_nonneg : 0 ≤ v / (b ^ 2 + v ^ 2) :=
      div_nonneg hv_nonneg hden_pos.le
    have hsin_abs_le_v : |Real.sin v| ≤ v := by
      calc
        |Real.sin v| ≤ |v| := Real.abs_sin_le_abs v
        _ = v := by
          exact abs_of_nonneg hv_nonneg
    have hv_sq_le_den : v ^ 2 ≤ b ^ 2 + v ^ 2 :=
      le_add_of_nonneg_left (sq_nonneg b)
    have hcoeff_v_le_one :
        (v / (b ^ 2 + v ^ 2)) * v ≤ 1 := by
      calc
        (v / (b ^ 2 + v ^ 2)) * v =
            (v * v) / (b ^ 2 + v ^ 2) := by
            exact div_mul_eq_mul_div v v (b ^ 2 + v ^ 2)
        _ = v ^ 2 / (b ^ 2 + v ^ 2) := by
            exact congrArg
              (fun r : ℝ => r / (b ^ 2 + v ^ 2))
              (pow_two v).symm
        _ ≤ 1 := by
            exact (div_le_one hden_pos).mpr hv_sq_le_den
    have habs :
        |f v| ≤ 1 := by
      calc
        |f v| =
            |v / (b ^ 2 + v ^ 2)| * |Real.sin v| := by
            unfold f
            exact abs_mul (v / (b ^ 2 + v ^ 2)) (Real.sin v)
        _ =
            (v / (b ^ 2 + v ^ 2)) * |Real.sin v| := by
            exact congrArg
              (fun r : ℝ => r * |Real.sin v|)
              (abs_of_nonneg hcoeff_nonneg)
        _ ≤ (v / (b ^ 2 + v ^ 2)) * v := by
            exact mul_le_mul_of_nonneg_left hsin_abs_le_v hcoeff_nonneg
        _ ≤ 1 := hcoeff_v_le_one
    calc
      ‖f v‖ = |f v| := by
        exact Real.norm_eq_abs (f v)
      _ ≤ 1 := habs
  have hnorm :
      ‖∫ v in b..A, f v‖ ≤ (1 : ℝ) * |A - b| :=
    intervalIntegral.norm_integral_le_of_norm_le_const hpoint
  have hlength : |A - b| ≤ 1 := by
    have hdiff_nonneg : 0 ≤ A - b :=
      sub_nonneg.mpr hbA
    have hdiff_le_A : A - b ≤ A :=
      sub_le_self A hb.le
    calc
      |A - b| = A - b := by
        exact abs_of_nonneg hdiff_nonneg
      _ ≤ A := hdiff_le_A
      _ ≤ 1 := hA_le_one
  have htarget :
      ‖∫ v in b..A, f v‖ ≤ 1 := by
    calc
      ‖∫ v in b..A, f v‖ ≤ (1 : ℝ) * |A - b| := hnorm
      _ = |A - b| := by
        exact one_mul |A - b|
      _ ≤ 1 := hlength
  calc
    |∫ v in (b)..A,
      (v / (b ^ 2 + v ^ 2)) * Real.sin v|
        = ‖∫ v in b..A, f v‖ := by
          unfold f
          exact (Real.norm_eq_abs
            (∫ v in b..A,
              (v / (b ^ 2 + v ^ 2)) * Real.sin v)).symm
    _ ≤ 1 := htarget

theorem scalarFourierLaplacePlemelj_dampedSineIntegral_tail_high_abs_le_two
    (A b c : ℝ) (hb : 0 < b) (hone_le_c : 1 ≤ c)
    (hb_le_c : b ≤ c) (hcA : c ≤ A) :
    |∫ v in c..A,
      (v / (b ^ 2 + v ^ 2)) * Real.sin v| ≤ 2 := by
  sorry

theorem scalarFourierLaplacePlemelj_dampedSineIntegral_tail_split_at_one
    (A b : ℝ) (hb : 0 < b) (hb_le_one : b ≤ 1)
    (hone_le_A : 1 ≤ A) :
    (∫ v in b..A,
      (v / (b ^ 2 + v ^ 2)) * Real.sin v) =
      (∫ v in b..1,
        (v / (b ^ 2 + v ^ 2)) * Real.sin v) +
        ∫ v in (1 : ℝ)..A,
          (v / (b ^ 2 + v ^ 2)) * Real.sin v := by
  let f : ℝ → ℝ :=
    fun v : ℝ => (v / (b ^ 2 + v ^ 2)) * Real.sin v
  have hden_cont : Continuous (fun v : ℝ => b ^ 2 + v ^ 2) :=
    continuous_const.add (continuous_id.pow 2)
  have hden_ne : ∀ v : ℝ, b ^ 2 + v ^ 2 ≠ 0 := by
    intro v
    exact
      scalarFourierLaplacePlemelj_zero_denominator_ne_zero b hb v
  have hquot_cont : Continuous (fun v : ℝ => v / (b ^ 2 + v ^ 2)) :=
    continuous_id.div hden_cont hden_ne
  have hf_cont : Continuous f := by
    unfold f
    exact hquot_cont.mul Real.continuous_sin
  have hleft : IntervalIntegrable f volume b 1 :=
    hf_cont.intervalIntegrable b 1
  have hright : IntervalIntegrable f volume (1 : ℝ) A :=
    hf_cont.intervalIntegrable 1 A
  calc
    (∫ v in b..A,
      (v / (b ^ 2 + v ^ 2)) * Real.sin v)
        = ∫ v in b..A, f v := by
          unfold f
          rfl
    _ =
        (∫ v in b..1, f v) + ∫ v in (1 : ℝ)..A, f v := by
          exact
            (intervalIntegral.integral_add_adjacent_intervals
              hleft hright).symm
    _ =
        (∫ v in b..1,
          (v / (b ^ 2 + v ^ 2)) * Real.sin v) +
          ∫ v in (1 : ℝ)..A,
            (v / (b ^ 2 + v ^ 2)) * Real.sin v := by
          unfold f
          rfl

theorem scalarFourierLaplacePlemelj_dampedSineIntegral_tail_high_abs_le_two_pi
    (A b c : ℝ) (hb : 0 < b) (hone_le_c : 1 ≤ c)
    (hb_le_c : b ≤ c) (hcA : c ≤ A) :
    |∫ v in c..A,
      (v / (b ^ 2 + v ^ 2)) * Real.sin v| ≤
      (2 : ℝ) * Real.pi := by
  exact
    (scalarFourierLaplacePlemelj_dampedSineIntegral_tail_high_abs_le_two
      A b c hb hone_le_c hb_le_c hcA).trans
        scalarFourierLaplacePlemelj_two_le_two_pi

theorem scalarFourierLaplacePlemelj_three_le_two_pi :
    (3 : ℝ) ≤ (2 : ℝ) * Real.pi := by
  have hpi_le_two_pi : Real.pi ≤ (2 : ℝ) * Real.pi := by
    calc
      Real.pi = (1 : ℝ) * Real.pi := by
        exact (one_mul Real.pi).symm
      _ ≤ (2 : ℝ) * Real.pi := by
        exact mul_le_mul_of_nonneg_right one_le_two Real.pi_pos.le
  exact Real.pi_gt_three.le.trans hpi_le_two_pi

theorem scalarFourierLaplacePlemelj_dampedSineIntegral_tail_crossing_abs_le_two_pi
    (A b : ℝ) (hb : 0 < b) (_hbA : b ≤ A)
    (hb_le_one : b ≤ 1) (hone_le_A : 1 ≤ A) :
    |∫ v in (b)..A,
      (v / (b ^ 2 + v ^ 2)) * Real.sin v| ≤
      (2 : ℝ) * Real.pi := by
  have hsplit :
      (∫ v in b..A,
        (v / (b ^ 2 + v ^ 2)) * Real.sin v) =
        (∫ v in b..1,
          (v / (b ^ 2 + v ^ 2)) * Real.sin v) +
          ∫ v in (1 : ℝ)..A,
            (v / (b ^ 2 + v ^ 2)) * Real.sin v :=
    scalarFourierLaplacePlemelj_dampedSineIntegral_tail_split_at_one
      A b hb hb_le_one hone_le_A
  have hlow :
      |∫ v in b..1,
        (v / (b ^ 2 + v ^ 2)) * Real.sin v| ≤ 1 :=
    scalarFourierLaplacePlemelj_dampedSineIntegral_tail_low_abs_le_one
      1 b hb hb_le_one (le_refl 1)
  have hhigh :
      |∫ v in (1 : ℝ)..A,
        (v / (b ^ 2 + v ^ 2)) * Real.sin v| ≤ 2 :=
    scalarFourierLaplacePlemelj_dampedSineIntegral_tail_high_abs_le_two
      A b 1 hb (le_refl 1) hb_le_one hone_le_A
  have hsum :
      |(∫ v in b..1,
        (v / (b ^ 2 + v ^ 2)) * Real.sin v) +
        ∫ v in (1 : ℝ)..A,
          (v / (b ^ 2 + v ^ 2)) * Real.sin v| ≤ 3 := by
    calc
      |(∫ v in b..1,
        (v / (b ^ 2 + v ^ 2)) * Real.sin v) +
        ∫ v in (1 : ℝ)..A,
          (v / (b ^ 2 + v ^ 2)) * Real.sin v|
          ≤
          |∫ v in b..1,
            (v / (b ^ 2 + v ^ 2)) * Real.sin v| +
            |∫ v in (1 : ℝ)..A,
              (v / (b ^ 2 + v ^ 2)) * Real.sin v| := by
            exact abs_add
              (∫ v in b..1,
                (v / (b ^ 2 + v ^ 2)) * Real.sin v)
              (∫ v in (1 : ℝ)..A,
                (v / (b ^ 2 + v ^ 2)) * Real.sin v)
      _ ≤ 1 + 2 := by
            exact add_le_add hlow hhigh
      _ = 3 := by
            rfl
  calc
    |∫ v in (b)..A,
      (v / (b ^ 2 + v ^ 2)) * Real.sin v|
        =
        |(∫ v in b..1,
          (v / (b ^ 2 + v ^ 2)) * Real.sin v) +
          ∫ v in (1 : ℝ)..A,
            (v / (b ^ 2 + v ^ 2)) * Real.sin v| := by
          exact congrArg abs hsplit
    _ ≤ 3 := hsum
    _ ≤ (2 : ℝ) * Real.pi :=
        scalarFourierLaplacePlemelj_three_le_two_pi

theorem scalarFourierLaplacePlemelj_dampedSineIntegral_tail_abs_le_two_pi
    (A b : ℝ) (hb : 0 < b) (hbA : b ≤ A) :
    |∫ v in (b)..A,
      (v / (b ^ 2 + v ^ 2)) * Real.sin v| ≤
      (2 : ℝ) * Real.pi := by
  match le_or_gt A 1 with
  | Or.inl hA_le_one =>
      have hlow :
          |∫ v in (b)..A,
            (v / (b ^ 2 + v ^ 2)) * Real.sin v| ≤ 1 :=
        scalarFourierLaplacePlemelj_dampedSineIntegral_tail_low_abs_le_one
          A b hb hbA hA_le_one
      exact hlow.trans scalarFourierLaplacePlemelj_one_le_two_pi
  | Or.inr hone_lt_A =>
      match le_or_gt b 1 with
      | Or.inl hb_le_one =>
          exact
            scalarFourierLaplacePlemelj_dampedSineIntegral_tail_crossing_abs_le_two_pi
              A b hb hbA hb_le_one (le_of_lt hone_lt_A)
      | Or.inr hone_lt_b =>
          exact
            scalarFourierLaplacePlemelj_dampedSineIntegral_tail_high_abs_le_two_pi
              A b b hb (le_of_lt hone_lt_b) (le_refl b) hbA

theorem scalarFourierLaplacePlemelj_dampedSineIntegral_split_at_scale
    (A b : ℝ) (hb : 0 < b) (hbA : b ≤ A) :
    (∫ v in (0)..A,
      (v / (b ^ 2 + v ^ 2)) * Real.sin v) =
      (∫ v in (0)..b,
        (v / (b ^ 2 + v ^ 2)) * Real.sin v) +
        ∫ v in b..A,
          (v / (b ^ 2 + v ^ 2)) * Real.sin v := by
  let f : ℝ → ℝ :=
    fun v : ℝ => (v / (b ^ 2 + v ^ 2)) * Real.sin v
  have hden_cont : Continuous (fun v : ℝ => b ^ 2 + v ^ 2) :=
    continuous_const.add (continuous_id.pow 2)
  have hden_ne : ∀ v : ℝ, b ^ 2 + v ^ 2 ≠ 0 := by
    intro v
    exact
      scalarFourierLaplacePlemelj_zero_denominator_ne_zero b hb v
  have hquot_cont : Continuous (fun v : ℝ => v / (b ^ 2 + v ^ 2)) :=
    continuous_id.div hden_cont hden_ne
  have hf_cont : Continuous f := by
    unfold f
    exact hquot_cont.mul Real.continuous_sin
  have hleft : IntervalIntegrable f volume 0 b :=
    hf_cont.intervalIntegrable 0 b
  have hright : IntervalIntegrable f volume b A :=
    hf_cont.intervalIntegrable b A
  calc
    (∫ v in (0)..A,
      (v / (b ^ 2 + v ^ 2)) * Real.sin v)
        = ∫ v in (0)..A, f v := by
          unfold f
          rfl
    _ =
        (∫ v in (0)..b, f v) + ∫ v in b..A, f v := by
          exact
            (intervalIntegral.integral_add_adjacent_intervals
              hleft hright).symm
    _ =
        (∫ v in (0)..b,
          (v / (b ^ 2 + v ^ 2)) * Real.sin v) +
          ∫ v in b..A,
            (v / (b ^ 2 + v ^ 2)) * Real.sin v := by
          unfold f
          rfl

theorem scalarFourierLaplacePlemelj_dampedSineIntegral_abs_le_one_add_two_pi
    (A b : ℝ) (hA : 0 ≤ A) (hb : 0 < b) :
    |∫ v in (0)..A,
      (v / (b ^ 2 + v ^ 2)) * Real.sin v| ≤
      1 + (2 : ℝ) * Real.pi := by
  match le_or_gt A b with
  | Or.inl hA_le_b =>
      have hsmall :
          |∫ v in (0)..A,
            (v / (b ^ 2 + v ^ 2)) * Real.sin v| ≤ 1 :=
        scalarFourierLaplacePlemelj_dampedSineIntegral_smallPrefix_abs_le_one
          A b hA hA_le_b hb
      have hone_le_target :
          (1 : ℝ) ≤ 1 + (2 : ℝ) * Real.pi :=
        le_add_of_nonneg_right (mul_nonneg zero_le_two Real.pi_pos.le)
      exact hsmall.trans hone_le_target
  | Or.inr hb_lt_A =>
      have hbA : b ≤ A :=
        le_of_lt hb_lt_A
      have hsplit :
          (∫ v in (0)..A,
            (v / (b ^ 2 + v ^ 2)) * Real.sin v) =
            (∫ v in (0)..b,
              (v / (b ^ 2 + v ^ 2)) * Real.sin v) +
              ∫ v in b..A,
                (v / (b ^ 2 + v ^ 2)) * Real.sin v :=
        scalarFourierLaplacePlemelj_dampedSineIntegral_split_at_scale
          A b hb hbA
      have hsmall :
          |∫ v in (0)..b,
            (v / (b ^ 2 + v ^ 2)) * Real.sin v| ≤ 1 :=
        scalarFourierLaplacePlemelj_dampedSineIntegral_smallPrefix_abs_le_one
          b b hb.le (le_refl b) hb
      have htail :
          |∫ v in (b)..A,
            (v / (b ^ 2 + v ^ 2)) * Real.sin v| ≤
            (2 : ℝ) * Real.pi :=
        scalarFourierLaplacePlemelj_dampedSineIntegral_tail_abs_le_two_pi
          A b hb hbA
      have hsum :
          |(∫ v in (0)..b,
            (v / (b ^ 2 + v ^ 2)) * Real.sin v) +
            ∫ v in b..A,
              (v / (b ^ 2 + v ^ 2)) * Real.sin v| ≤
            1 + (2 : ℝ) * Real.pi := by
        calc
          |(∫ v in (0)..b,
            (v / (b ^ 2 + v ^ 2)) * Real.sin v) +
            ∫ v in b..A,
              (v / (b ^ 2 + v ^ 2)) * Real.sin v|
              ≤
              |∫ v in (0)..b,
                (v / (b ^ 2 + v ^ 2)) * Real.sin v| +
                |∫ v in b..A,
                  (v / (b ^ 2 + v ^ 2)) * Real.sin v| := by
                exact abs_add
                  (∫ v in (0)..b,
                    (v / (b ^ 2 + v ^ 2)) * Real.sin v)
                  (∫ v in b..A,
                    (v / (b ^ 2 + v ^ 2)) * Real.sin v)
          _ ≤ 1 + (2 : ℝ) * Real.pi := by
                exact add_le_add hsmall htail
      calc
        |∫ v in (0)..A,
          (v / (b ^ 2 + v ^ 2)) * Real.sin v|
            =
            |(∫ v in (0)..b,
              (v / (b ^ 2 + v ^ 2)) * Real.sin v) +
              ∫ v in b..A,
                (v / (b ^ 2 + v ^ 2)) * Real.sin v| := by
              exact congrArg abs hsplit
        _ ≤ 1 + (2 : ℝ) * Real.pi := hsum

/-- Positive-frequency change of variables `v = y*u` for the normalized
Hilbert-sine kernel. -/
theorem scalarFourierLaplacePlemelj_normalizedHalfHilbertSineKernel_eq_dampedSineIntegral
    (R y : ℝ) (hy : 0 < y) :
    (∫ u in (0)..R,
      (u / (1 + u ^ 2)) * Real.sin (y * u)) =
      ∫ v in (0)..(y * R),
        (v / (y ^ 2 + v ^ 2)) * Real.sin v := by
  let G : ℝ → ℝ :=
    fun v : ℝ => (v / (y ^ 2 + v ^ 2)) * Real.sin v
  have hpoint :
      ∀ u : ℝ,
        (u / (1 + u ^ 2)) * Real.sin (y * u) =
          y * G (u * y) := by
    intro u
    have hcoeff :
        y * ((u * y) / (y ^ 2 + (u * y) ^ 2)) =
          u / (1 + u ^ 2) :=
      scalarFourierLaplacePlemelj_scaledHilbertSineKernel_coefficient_identity
        y hy u
    calc
      (u / (1 + u ^ 2)) * Real.sin (y * u)
          =
          (y * ((u * y) / (y ^ 2 + (u * y) ^ 2))) *
            Real.sin (y * u) := by
            exact congrArg
              (fun r : ℝ => r * Real.sin (y * u))
              hcoeff.symm
      _ =
          y *
            (((u * y) / (y ^ 2 + (u * y) ^ 2)) *
              Real.sin (u * y)) := by
            have hphase : Real.sin (y * u) = Real.sin (u * y) :=
              congrArg Real.sin (mul_comm y u)
            calc
              (y * ((u * y) / (y ^ 2 + (u * y) ^ 2))) *
                  Real.sin (y * u)
                  =
                  (y * ((u * y) / (y ^ 2 + (u * y) ^ 2))) *
                    Real.sin (u * y) := by
                    exact congrArg
                      (fun s : ℝ =>
                        (y * ((u * y) / (y ^ 2 + (u * y) ^ 2))) * s)
                      hphase
              _ =
                  y *
                    (((u * y) / (y ^ 2 + (u * y) ^ 2)) *
                      Real.sin (u * y)) := by
                    exact mul_assoc y
                      ((u * y) / (y ^ 2 + (u * y) ^ 2))
                      (Real.sin (u * y))
      _ = y * G (u * y) := by
            unfold G
            rfl
  have hconst :
      (∫ u in (0)..R,
        (u / (1 + u ^ 2)) * Real.sin (y * u)) =
        y * ∫ u in (0)..R, G (u * y) := by
    calc
      (∫ u in (0)..R,
        (u / (1 + u ^ 2)) * Real.sin (y * u))
          = ∫ u in (0)..R, y * G (u * y) := by
            exact intervalIntegral.integral_congr
              (Filter.Eventually.of_forall hpoint)
      _ = y * ∫ u in (0)..R, G (u * y) := by
            exact intervalIntegral.integral_const_mul
              (a := 0) (b := R) (μ := volume)
              y
              (fun u : ℝ => G (u * y))
  have hsubst :
      y * ∫ u in (0)..R, G (u * y) =
        ∫ v in (0 * y)..(R * y), G v :=
    intervalIntegral.smul_integral_comp_mul_right
      (f := G) (a := 0) (b := R) y
  calc
    (∫ u in (0)..R,
      (u / (1 + u ^ 2)) * Real.sin (y * u))
        = y * ∫ u in (0)..R, G (u * y) := hconst
    _ = ∫ v in (0 * y)..(R * y), G v := hsubst
    _ = ∫ v in (0)..(y * R), G v := by
          exact congrArg₂
            (fun l r : ℝ => ∫ v in l..r, G v)
            (zero_mul y)
            (mul_comm R y)
    _ =
        ∫ v in (0)..(y * R),
          (v / (y ^ 2 + v ^ 2)) * Real.sin v := by
          unfold G
          rfl

theorem scalarFourierLaplacePlemelj_normalizedHalfHilbertSineKernel_abs_le_one_add_two_pi_of_nonneg_radius_pos_frequency
    (R y : ℝ) (hR : 0 ≤ R) (hy : 0 < y) :
    |∫ u in (0)..R,
      (u / (1 + u ^ 2)) * Real.sin (y * u)| ≤
      1 + (2 : ℝ) * Real.pi := by
  have hA_nonneg : 0 ≤ y * R :=
    mul_nonneg hy.le hR
  have hscale :
      (∫ u in (0)..R,
        (u / (1 + u ^ 2)) * Real.sin (y * u)) =
        ∫ v in (0)..(y * R),
          (v / (y ^ 2 + v ^ 2)) * Real.sin v :=
    scalarFourierLaplacePlemelj_normalizedHalfHilbertSineKernel_eq_dampedSineIntegral
      R y hy
  calc
    |∫ u in (0)..R,
      (u / (1 + u ^ 2)) * Real.sin (y * u)|
        =
        |∫ v in (0)..(y * R),
          (v / (y ^ 2 + v ^ 2)) * Real.sin v| := by
          exact congrArg abs hscale
    _ ≤ 1 + (2 : ℝ) * Real.pi :=
        scalarFourierLaplacePlemelj_dampedSineIntegral_abs_le_one_add_two_pi
          (y * R) y hA_nonneg hy

/-- The normalized Hilbert-sine kernel is even in the integration variable. -/
theorem scalarFourierLaplacePlemelj_normalizedHalfHilbertSineKernel_integrand_even
    (y u : ℝ) :
    ((-u) / (1 + (-u) ^ 2)) * Real.sin (y * (-u)) =
      (u / (1 + u ^ 2)) * Real.sin (y * u) := by
  have hden : 1 + (-u) ^ 2 = 1 + u ^ 2 := by
    exact congrArg (fun r : ℝ => 1 + r) (neg_sq u)
  have harg : y * (-u) = -(y * u) :=
    mul_neg y u
  have hsin : Real.sin (y * (-u)) = -Real.sin (y * u) :=
    (congrArg Real.sin harg).trans (Real.sin_neg (y * u))
  have hquot :
      (-u) / (1 + (-u) ^ 2) = -(u / (1 + u ^ 2)) := by
    calc
      (-u) / (1 + (-u) ^ 2)
          = (-u) / (1 + u ^ 2) := by
            exact congrArg (fun d : ℝ => (-u) / d) hden
      _ = -(u / (1 + u ^ 2)) := by
            exact neg_div u (1 + u ^ 2)
  calc
    ((-u) / (1 + (-u) ^ 2)) * Real.sin (y * (-u))
        = (-(u / (1 + u ^ 2))) * Real.sin (y * (-u)) := by
          exact congrArg
            (fun r : ℝ => r * Real.sin (y * (-u)))
            hquot
    _ = (-(u / (1 + u ^ 2))) * (-Real.sin (y * u)) := by
          exact congrArg
            (fun s : ℝ => (-(u / (1 + u ^ 2))) * s)
            hsin
    _ = (u / (1 + u ^ 2)) * Real.sin (y * u) := by
          exact neg_mul_neg (u / (1 + u ^ 2)) (Real.sin (y * u))

/-- Positive-frequency normalized half-window Hilbert-sine Dirichlet bound. -/
theorem scalarFourierLaplacePlemelj_normalizedHalfHilbertSineKernel_abs_le_one_add_two_pi_of_pos_frequency
    (R y : ℝ) (hy : 0 < y) :
    |∫ u in (0)..R,
      (u / (1 + u ^ 2)) * Real.sin (y * u)| ≤
      1 + (2 : ℝ) * Real.pi := by
  match le_or_gt 0 R with
  | Or.inl hR =>
      exact
        scalarFourierLaplacePlemelj_normalizedHalfHilbertSineKernel_abs_le_one_add_two_pi_of_nonneg_radius_pos_frequency
          R y hR hy
  | Or.inr hR_neg =>
      let S : ℝ := -R
      let F : ℝ → ℝ :=
        fun u : ℝ => (u / (1 + u ^ 2)) * Real.sin (y * u)
      have hS_nonneg : 0 ≤ S := by
        unfold S
        exact neg_nonneg.mpr (le_of_lt hR_neg)
      have hcomp :
          (∫ u in (0)..S, F (-u)) = ∫ u in R..0, F u := by
        have hR_eq : R = -S := by
          unfold S
          exact (neg_neg R).symm
        calc
          (∫ u in (0)..S, F (-u))
              = ∫ u in (-S)..0, F u := by
                exact intervalIntegral.integral_comp_neg
                  (f := F) (a := 0) (b := S)
          _ = ∫ u in R..0, F u := by
                exact congrArg
                  (fun l : ℝ => ∫ u in l..0, F u)
                  hR_eq.symm
      have heven :
          (∫ u in (0)..S, F (-u)) = ∫ u in (0)..S, F u := by
        exact intervalIntegral.integral_congr
          (Filter.Eventually.of_forall
            (fun u : ℝ => by
              unfold F
              exact
                scalarFourierLaplacePlemelj_normalizedHalfHilbertSineKernel_integrand_even
                  y u))
      have hR_to_S :
          (∫ u in (0)..R, F u) = -∫ u in (0)..S, F u := by
        calc
          (∫ u in (0)..R, F u)
              = -∫ u in R..0, F u := by
                exact intervalIntegral.integral_symm R 0
          _ = -∫ u in (0)..S, F (-u) := by
                exact congrArg Neg.neg hcomp.symm
          _ = -∫ u in (0)..S, F u := by
                exact congrArg Neg.neg heven
      have hS_bound :
          |∫ u in (0)..S, F u| ≤ 1 + (2 : ℝ) * Real.pi := by
        unfold F
        exact
          scalarFourierLaplacePlemelj_normalizedHalfHilbertSineKernel_abs_le_one_add_two_pi_of_nonneg_radius_pos_frequency
            S y hS_nonneg hy
      calc
        |∫ u in (0)..R,
          (u / (1 + u ^ 2)) * Real.sin (y * u)|
            = |∫ u in (0)..R, F u| := by
              unfold F
              rfl
        _ = |-∫ u in (0)..S, F u| := by
              exact congrArg abs hR_to_S
        _ = |∫ u in (0)..S, F u| := by
              exact abs_neg (∫ u in (0)..S, F u)
        _ ≤ 1 + (2 : ℝ) * Real.pi := hS_bound

/-- Changing the sign of the frequency negates the normalized half-window
Hilbert-sine integral. -/
theorem scalarFourierLaplacePlemelj_normalizedHalfHilbertSineKernel_neg_frequency
    (R y : ℝ) :
    (∫ u in (0)..R,
      (u / (1 + u ^ 2)) * Real.sin ((-y) * u)) =
      -∫ u in (0)..R,
        (u / (1 + u ^ 2)) * Real.sin (y * u) := by
  let F : ℝ → ℝ :=
    fun u : ℝ => (u / (1 + u ^ 2)) * Real.sin (y * u)
  have hpoint :
      ∀ u : ℝ,
        (u / (1 + u ^ 2)) * Real.sin ((-y) * u) = -F u := by
    intro u
    have harg : (-y) * u = -(y * u) :=
      neg_mul y u
    have hsin : Real.sin ((-y) * u) = -Real.sin (y * u) :=
      (congrArg Real.sin harg).trans (Real.sin_neg (y * u))
    calc
      (u / (1 + u ^ 2)) * Real.sin ((-y) * u)
          = (u / (1 + u ^ 2)) * (-Real.sin (y * u)) := by
            exact congrArg
              (fun s : ℝ => (u / (1 + u ^ 2)) * s)
              hsin
      _ = -((u / (1 + u ^ 2)) * Real.sin (y * u)) := by
            exact mul_neg (u / (1 + u ^ 2)) (Real.sin (y * u))
      _ = -F u := by
            unfold F
            rfl
  calc
    (∫ u in (0)..R,
      (u / (1 + u ^ 2)) * Real.sin ((-y) * u))
        = ∫ u in (0)..R, -F u := by
          exact intervalIntegral.integral_congr
            (Filter.Eventually.of_forall hpoint)
    _ = -∫ u in (0)..R, F u := by
          exact intervalIntegral.integral_neg
    _ =
        -∫ u in (0)..R,
          (u / (1 + u ^ 2)) * Real.sin (y * u) := by
          unfold F
          rfl

/-- Nonzero-frequency normalized half-window Hilbert-sine Dirichlet bound. -/
theorem scalarFourierLaplacePlemelj_normalizedHalfHilbertSineKernel_abs_le_one_add_two_pi_of_ne_zero
    (R y : ℝ) (hy : y ≠ 0) :
    |∫ u in (0)..R,
      (u / (1 + u ^ 2)) * Real.sin (y * u)| ≤
      1 + (2 : ℝ) * Real.pi := by
  match lt_or_gt_of_ne hy with
  | Or.inl hy_neg =>
      let yp : ℝ := -y
      have hyp_pos : 0 < yp := by
        unfold yp
        exact neg_pos.mpr hy_neg
      have hneg :
          (∫ u in (0)..R,
            (u / (1 + u ^ 2)) * Real.sin (y * u)) =
            -∫ u in (0)..R,
              (u / (1 + u ^ 2)) * Real.sin (yp * u) := by
        have hy_eq : y = -yp := by
          unfold yp
          exact (neg_neg y).symm
        calc
          (∫ u in (0)..R,
            (u / (1 + u ^ 2)) * Real.sin (y * u))
              =
              ∫ u in (0)..R,
                (u / (1 + u ^ 2)) * Real.sin ((-yp) * u) := by
                exact intervalIntegral.integral_congr
                  (Filter.Eventually.of_forall
                    (fun u : ℝ => by
                      exact congrArg
                        (fun z : ℝ =>
                          (u / (1 + u ^ 2)) * Real.sin (z * u))
                        hy_eq))
          _ =
              -∫ u in (0)..R,
                (u / (1 + u ^ 2)) * Real.sin (yp * u) := by
                exact
                  scalarFourierLaplacePlemelj_normalizedHalfHilbertSineKernel_neg_frequency
                    R yp
      have hpos :
          |∫ u in (0)..R,
            (u / (1 + u ^ 2)) * Real.sin (yp * u)| ≤
            1 + (2 : ℝ) * Real.pi :=
        scalarFourierLaplacePlemelj_normalizedHalfHilbertSineKernel_abs_le_one_add_two_pi_of_pos_frequency
          R yp hyp_pos
      calc
        |∫ u in (0)..R,
          (u / (1 + u ^ 2)) * Real.sin (y * u)|
            =
            |-∫ u in (0)..R,
              (u / (1 + u ^ 2)) * Real.sin (yp * u)| := by
              exact congrArg abs hneg
        _ =
            |∫ u in (0)..R,
              (u / (1 + u ^ 2)) * Real.sin (yp * u)| := by
              exact abs_neg
                (∫ u in (0)..R,
                  (u / (1 + u ^ 2)) * Real.sin (yp * u))
        _ ≤ 1 + (2 : ℝ) * Real.pi := hpos
  | Or.inr hy_pos =>
      exact
        scalarFourierLaplacePlemelj_normalizedHalfHilbertSineKernel_abs_le_one_add_two_pi_of_pos_frequency
          R y hy_pos

theorem scalarFourierLaplacePlemelj_normalizedHalfHilbertSineKernel_abs_le_one_add_two_pi
    (R y : ℝ) :
    |∫ u in (0)..R,
      (u / (1 + u ^ 2)) * Real.sin (y * u)| ≤
      1 + (2 : ℝ) * Real.pi := by
  match eq_or_ne y 0 with
  | Or.inl hy =>
      have hzero :
          (∫ u in (0)..R,
            (u / (1 + u ^ 2)) * Real.sin (y * u)) = 0 := by
        calc
          (∫ u in (0)..R,
            (u / (1 + u ^ 2)) * Real.sin (y * u))
              =
              ∫ u in (0)..R,
                (u / (1 + u ^ 2)) * Real.sin (0 * u) := by
                exact intervalIntegral.integral_congr
                  (Filter.Eventually.of_forall
                    (fun u : ℝ => by
                      exact congrArg
                        (fun z : ℝ =>
                          (u / (1 + u ^ 2)) * Real.sin (z * u))
                        hy))
          _ =
              ∫ u in (0)..R, 0 := by
                exact intervalIntegral.integral_congr
                  (Filter.Eventually.of_forall
                    (fun u : ℝ => by
                      exact mul_zero (u / (1 + u ^ 2))))
          _ = 0 := by
                exact intervalIntegral.integral_zero
      have htarget : |(0 : ℝ)| ≤ 1 + (2 : ℝ) * Real.pi := by
        have hC_nonneg : 0 ≤ 1 + (2 : ℝ) * Real.pi :=
          add_nonneg zero_le_one (mul_nonneg zero_le_two Real.pi_pos.le)
        exact (abs_zero : |(0 : ℝ)| = 0).le.trans hC_nonneg
      exact Eq.subst
        (motive := fun z : ℝ => |z| ≤ 1 + (2 : ℝ) * Real.pi)
        hzero.symm
        htarget
  | Or.inr hy =>
      exact
        scalarFourierLaplacePlemelj_normalizedHalfHilbertSineKernel_abs_le_one_add_two_pi_of_ne_zero
          R y hy

/-- Scaling reduction from the width-`a` Hilbert-Cauchy sine kernel to the
normalized kernel `u / (1 + u^2)`. -/
theorem scalarFourierLaplacePlemelj_scaledHilbertSineKernel_coefficient_identity
    (a : ℝ) (ha : 0 < a) (u : ℝ) :
    a * ((u * a) / (a ^ 2 + (u * a) ^ 2)) =
      u / (1 + u ^ 2) := by
  have ha_ne : a ≠ 0 :=
    ne_of_gt ha
  have ha_sq_ne : a ^ 2 ≠ 0 := by
    exact pow_ne_zero 2 ha_ne
  have hnum : a * (u * a) = u * a ^ 2 := by
    calc
      a * (u * a) = (a * u) * a := by
        exact (mul_assoc a u a).symm
      _ = (u * a) * a := by
        exact congrArg (fun r : ℝ => r * a) (mul_comm a u)
      _ = u * (a * a) := by
        exact mul_assoc u a a
      _ = u * a ^ 2 := by
        exact congrArg (fun r : ℝ => u * r) (sq a).symm
  have huasq : (u * a) ^ 2 = u ^ 2 * a ^ 2 := by
    exact mul_pow u a 2
  have hden : a ^ 2 + (u * a) ^ 2 = (1 + u ^ 2) * a ^ 2 := by
    calc
      a ^ 2 + (u * a) ^ 2
          = a ^ 2 + u ^ 2 * a ^ 2 := by
            exact congrArg (fun r : ℝ => a ^ 2 + r) huasq
      _ = 1 * a ^ 2 + u ^ 2 * a ^ 2 := by
            exact congrArg
              (fun r : ℝ => r + u ^ 2 * a ^ 2)
              (one_mul (a ^ 2)).symm
      _ = (1 + u ^ 2) * a ^ 2 := by
            exact (add_mul 1 (u ^ 2) (a ^ 2)).symm
  calc
    a * ((u * a) / (a ^ 2 + (u * a) ^ 2))
        = (a * (u * a)) / (a ^ 2 + (u * a) ^ 2) := by
          exact mul_div_assoc' a (u * a) (a ^ 2 + (u * a) ^ 2)
    _ = (u * a ^ 2) / (a ^ 2 + (u * a) ^ 2) := by
          exact congrArg
            (fun r : ℝ => r / (a ^ 2 + (u * a) ^ 2))
            hnum
    _ = (u * a ^ 2) / ((1 + u ^ 2) * a ^ 2) := by
          exact congrArg (fun r : ℝ => (u * a ^ 2) / r) hden
    _ = u / (1 + u ^ 2) := by
          exact mul_div_mul_right u (1 + u ^ 2) ha_sq_ne

theorem scalarFourierLaplacePlemelj_scaledHilbertSineKernel_phase_identity
    (a x u : ℝ) :
    Real.sin ((u * a) * x) = Real.sin ((a * x) * u) := by
  have harg : (u * a) * x = (a * x) * u := by
    calc
      (u * a) * x = u * (a * x) := by
        exact mul_assoc u a x
      _ = (a * x) * u := by
        exact mul_comm u (a * x)
  exact congrArg Real.sin harg

theorem scalarFourierLaplacePlemelj_halfHilbertSineKernel_scaled_integrand_identity
    (a : ℝ) (ha : 0 < a) (x u : ℝ) :
    a *
      (((u * a) / (a ^ 2 + (u * a) ^ 2)) *
        Real.sin ((u * a) * x)) =
      (u / (1 + u ^ 2)) * Real.sin ((a * x) * u) := by
  have hcoeff :
      a * ((u * a) / (a ^ 2 + (u * a) ^ 2)) =
        u / (1 + u ^ 2) :=
    scalarFourierLaplacePlemelj_scaledHilbertSineKernel_coefficient_identity
      a ha u
  have hphase :
      Real.sin ((u * a) * x) = Real.sin ((a * x) * u) :=
    scalarFourierLaplacePlemelj_scaledHilbertSineKernel_phase_identity
      a x u
  calc
    a *
      (((u * a) / (a ^ 2 + (u * a) ^ 2)) *
        Real.sin ((u * a) * x))
        =
        (a * ((u * a) / (a ^ 2 + (u * a) ^ 2))) *
          Real.sin ((u * a) * x) := by
          exact mul_assoc a
            ((u * a) / (a ^ 2 + (u * a) ^ 2))
            (Real.sin ((u * a) * x))
    _ =
        (u / (1 + u ^ 2)) *
          Real.sin ((u * a) * x) := by
          exact congrArg
            (fun r : ℝ => r * Real.sin ((u * a) * x))
            hcoeff
    _ =
        (u / (1 + u ^ 2)) * Real.sin ((a * x) * u) := by
          exact congrArg
            (fun s : ℝ => (u / (1 + u ^ 2)) * s)
            hphase

/-- Endpoint cancellation for the positive scaling `t = a*u`. -/
theorem scalarFourierLaplacePlemelj_halfHilbertSineKernel_scaled_endpoint
    (a : ℝ) (ha : 0 < a) (T : ℝ) :
    (T / a) * a = T := by
  exact div_mul_cancel₀ T (ne_of_gt ha)

/-- Change-of-variables form of the half-window Hilbert-Cauchy sine kernel
under `t = a*u`, before applying the pointwise algebra identity. -/
theorem scalarFourierLaplacePlemelj_halfHilbertSineKernel_eq_scaled_integral
    (a : ℝ) (ha : 0 < a) (T x : ℝ) :
    (∫ t in (0)..T,
      (t / (a ^ 2 + t ^ 2)) * Real.sin (t * x)) =
      a *
        ∫ u in (0)..(T / a),
          (((u * a) / (a ^ 2 + (u * a) ^ 2)) *
            Real.sin ((u * a) * x)) := by
  let F : ℝ → ℝ :=
    fun t : ℝ => (t / (a ^ 2 + t ^ 2)) * Real.sin (t * x)
  have hend : (T / a) * a = T :=
    scalarFourierLaplacePlemelj_halfHilbertSineKernel_scaled_endpoint
      a ha T
  have hsubst :
      a *
        ∫ u in (0)..(T / a), F (u * a) =
        ∫ t in (0 * a)..((T / a) * a), F t := by
    exact intervalIntegral.smul_integral_comp_mul_right
      (f := F) (a := 0) (b := T / a) a
  calc
    (∫ t in (0)..T,
      (t / (a ^ 2 + t ^ 2)) * Real.sin (t * x))
        = ∫ t in (0)..T, F t := by
          unfold F
          rfl
    _ = ∫ t in (0 * a)..((T / a) * a), F t := by
          exact congrArg₂
            (fun l r : ℝ => ∫ t in l..r, F t)
            (zero_mul a).symm
            hend.symm
    _ =
        a *
          ∫ u in (0)..(T / a), F (u * a) := by
          exact hsubst.symm
    _ =
        a *
          ∫ u in (0)..(T / a),
            (((u * a) / (a ^ 2 + (u * a) ^ 2)) *
              Real.sin ((u * a) * x)) := by
          unfold F
          rfl

theorem scalarFourierLaplacePlemelj_halfHilbertSineKernel_eq_normalized
    (a : ℝ) (ha : 0 < a) (T x : ℝ) :
    (∫ t in (0)..T,
      (t / (a ^ 2 + t ^ 2)) * Real.sin (t * x)) =
      ∫ u in (0)..(T / a),
        (u / (1 + u ^ 2)) * Real.sin ((a * x) * u) := by
  have hscale :
      (∫ t in (0)..T,
        (t / (a ^ 2 + t ^ 2)) * Real.sin (t * x)) =
        a *
          ∫ u in (0)..(T / a),
            (((u * a) / (a ^ 2 + (u * a) ^ 2)) *
              Real.sin ((u * a) * x)) :=
    scalarFourierLaplacePlemelj_halfHilbertSineKernel_eq_scaled_integral
      a ha T x
  have hpoint :
      ∀ u : ℝ,
        a *
          (((u * a) / (a ^ 2 + (u * a) ^ 2)) *
            Real.sin ((u * a) * x)) =
          (u / (1 + u ^ 2)) * Real.sin ((a * x) * u) :=
    fun u : ℝ =>
      scalarFourierLaplacePlemelj_halfHilbertSineKernel_scaled_integrand_identity
        a ha x u
  have hintegral :
      a *
        ∫ u in (0)..(T / a),
          (((u * a) / (a ^ 2 + (u * a) ^ 2)) *
            Real.sin ((u * a) * x)) =
        ∫ u in (0)..(T / a),
          (u / (1 + u ^ 2)) * Real.sin ((a * x) * u) := by
    calc
      a *
        ∫ u in (0)..(T / a),
          (((u * a) / (a ^ 2 + (u * a) ^ 2)) *
            Real.sin ((u * a) * x))
          =
          ∫ u in (0)..(T / a),
            a *
              (((u * a) / (a ^ 2 + (u * a) ^ 2)) *
                Real.sin ((u * a) * x)) := by
            exact (intervalIntegral.integral_const_mul
              (a := 0) (b := T / a) (μ := volume)
              a
              (fun u : ℝ =>
                (((u * a) / (a ^ 2 + (u * a) ^ 2)) *
                  Real.sin ((u * a) * x))).symm
      _ =
          ∫ u in (0)..(T / a),
            (u / (1 + u ^ 2)) * Real.sin ((a * x) * u) := by
            exact intervalIntegral.integral_congr
              (Filter.Eventually.of_forall hpoint)
  exact hscale.trans hintegral

theorem scalarFourierLaplacePlemelj_halfHilbertSineKernel_abs_le_one_add_two_pi
    (a : ℝ) (ha : 0 < a) (T x : ℝ) :
    |∫ t in (0)..T,
      (t / (a ^ 2 + t ^ 2)) * Real.sin (t * x)| ≤
      1 + (2 : ℝ) * Real.pi := by
  have hscale :
      (∫ t in (0)..T,
        (t / (a ^ 2 + t ^ 2)) * Real.sin (t * x)) =
        ∫ u in (0)..(T / a),
          (u / (1 + u ^ 2)) * Real.sin ((a * x) * u) :=
    scalarFourierLaplacePlemelj_halfHilbertSineKernel_eq_normalized
      a ha T x
  calc
    |∫ t in (0)..T,
      (t / (a ^ 2 + t ^ 2)) * Real.sin (t * x)|
        =
        |∫ u in (0)..(T / a),
          (u / (1 + u ^ 2)) * Real.sin ((a * x) * u)| := by
          exact congrArg abs hscale
    _ ≤ 1 + (2 : ℝ) * Real.pi :=
        scalarFourierLaplacePlemelj_normalizedHalfHilbertSineKernel_abs_le_one_add_two_pi
          (T / a) (a * x)


/-- Symmetric finite windows of the Hilbert-Cauchy sine kernel reduce to twice
the positive half-window because the kernel is even. -/
theorem scalarFourierLaplacePlemelj_finiteHilbertSineKernel_symmetric_eq_two_half
    (a : ℝ) (ha : 0 < a) (T x : ℝ) :
    (∫ t in Set.Icc (-T) T,
      (t / (a ^ 2 + t ^ 2)) * Real.sin (t * x)) =
      (2 : ℝ) *
        ∫ t in (0)..T,
          (t / (a ^ 2 + t ^ 2)) * Real.sin (t * x) := by
  let f : ℝ → ℝ :=
    fun t : ℝ => (t / (a ^ 2 + t ^ 2)) * Real.sin (t * x)
  have hden_cont : Continuous (fun t : ℝ => a ^ 2 + t ^ 2) :=
    continuous_const.add (continuous_id.pow 2)
  have hden_ne : ∀ t : ℝ, a ^ 2 + t ^ 2 ≠ 0 :=
    scalarFourierLaplacePlemelj_zero_denominator_ne_zero a ha
  have hquot_cont : Continuous (fun t : ℝ => t / (a ^ 2 + t ^ 2)) :=
    continuous_id.div hden_cont hden_ne
  have htx_cont : Continuous (fun t : ℝ => t * x) :=
    continuous_id.mul continuous_const
  have hsin_cont : Continuous (fun t : ℝ => Real.sin (t * x)) :=
    Real.continuous_sin.comp htx_cont
  have hf_cont : Continuous f := by
    unfold f
    exact hquot_cont.mul hsin_cont
  have hf_left : IntervalIntegrable f volume (-T) 0 :=
    hf_cont.intervalIntegrable (-T) 0
  have hf_right : IntervalIntegrable f volume 0 T :=
    hf_cont.intervalIntegrable 0 T
  have heven : ∀ t : ℝ, f (-t) = f t := by
    intro t
    unfold f
    have hden :
        a ^ 2 + (-t) ^ 2 = a ^ 2 + t ^ 2 := by
      exact congrArg (fun u : ℝ => a ^ 2 + u) (neg_sq t)
    have harg : (-t) * x = -(t * x) :=
      neg_mul t x
    have hsin : Real.sin ((-t) * x) = -Real.sin (t * x) := by
      exact (congrArg Real.sin harg).trans (Real.sin_neg (t * x))
    have hdiv :
        (-t) / (a ^ 2 + (-t) ^ 2) =
          -(t / (a ^ 2 + t ^ 2)) := by
      calc
        (-t) / (a ^ 2 + (-t) ^ 2)
            = (-t) / (a ^ 2 + t ^ 2) := by
              exact congrArg (fun d : ℝ => (-t) / d) hden
        _ = -(t / (a ^ 2 + t ^ 2)) := by
              exact neg_div t (a ^ 2 + t ^ 2)
    calc
      ((-t) / (a ^ 2 + (-t) ^ 2)) * Real.sin ((-t) * x)
          =
          (-(t / (a ^ 2 + t ^ 2))) * Real.sin ((-t) * x) := by
            exact congrArg
              (fun r : ℝ => r * Real.sin ((-t) * x))
              hdiv
      _ =
          (-(t / (a ^ 2 + t ^ 2))) * (-Real.sin (t * x)) := by
            exact congrArg
              (fun r : ℝ => (-(t / (a ^ 2 + t ^ 2))) * r)
              hsin
      _ =
          (t / (a ^ 2 + t ^ 2)) * Real.sin (t * x) := by
            exact neg_mul_neg (t / (a ^ 2 + t ^ 2)) (Real.sin (t * x))
  have hleft_eq_right :
      (∫ t in (-T)..0, f t) = ∫ t in (0)..T, f t := by
    have hcomp :
        (∫ t in (0)..T, f (-t)) = ∫ t in (-T)..0, f t := by
      exact
        intervalIntegral.integral_comp_neg
          (f := f) (a := 0) (b := T)
    have hcomp_even :
        (∫ t in (0)..T, f (-t)) = ∫ t in (0)..T, f t := by
      exact
        intervalIntegral.integral_congr
          (Filter.Eventually.of_forall heven)
    exact hcomp.symm.trans hcomp_even
  have hsplit :
      (∫ t in (-T)..T, f t) =
        (∫ t in (-T)..0, f t) + ∫ t in (0)..T, f t := by
    exact
      (intervalIntegral.integral_add_adjacent_intervals
        hf_left hf_right).symm
  calc
    (∫ t in Set.Icc (-T) T,
      (t / (a ^ 2 + t ^ 2)) * Real.sin (t * x))
        = ∫ t in (-T)..T, f t := by
          unfold f
          rfl
    _ = (∫ t in (-T)..0, f t) + ∫ t in (0)..T, f t := hsplit
    _ = (∫ t in (0)..T, f t) + ∫ t in (0)..T, f t := by
          exact congrArg
            (fun y : ℝ => y + ∫ t in (0)..T, f t)
            hleft_eq_right
    _ = (2 : ℝ) * ∫ t in (0)..T, f t := by
          exact (two_mul (∫ t in (0)..T, f t)).symm
    _ =
        (2 : ℝ) *
          ∫ t in (0)..T,
            (t / (a ^ 2 + t ^ 2)) * Real.sin (t * x) := by
          unfold f
          rfl

/-- Finite-window Dirichlet bound for the odd Hilbert-Cauchy sine kernel. -/
theorem scalarFourierLaplacePlemelj_finiteHilbertSineKernel_abs_le_two_add_four_pi
    (a : ℝ) (ha : 0 < a) (T x : ℝ) :
    |∫ t in Set.Icc (-T) T,
      (t / (a ^ 2 + t ^ 2)) * Real.sin (t * x)| ≤
      (2 : ℝ) * (1 + (2 : ℝ) * Real.pi) := by
  have hsym :
      (∫ t in Set.Icc (-T) T,
        (t / (a ^ 2 + t ^ 2)) * Real.sin (t * x)) =
        (2 : ℝ) *
          ∫ t in (0)..T,
            (t / (a ^ 2 + t ^ 2)) * Real.sin (t * x) :=
    scalarFourierLaplacePlemelj_finiteHilbertSineKernel_symmetric_eq_two_half
      a ha T x
  have hhalf :
      |∫ t in (0)..T,
        (t / (a ^ 2 + t ^ 2)) * Real.sin (t * x)| ≤
        1 + (2 : ℝ) * Real.pi :=
    scalarFourierLaplacePlemelj_halfHilbertSineKernel_abs_le_one_add_two_pi
      a ha T x
  have htwo_nonneg : (0 : ℝ) ≤ 2 :=
    zero_le_two
  have htwo_abs :
      |(2 : ℝ) *
        ∫ t in (0)..T,
          (t / (a ^ 2 + t ^ 2)) * Real.sin (t * x)| =
        (2 : ℝ) *
          |∫ t in (0)..T,
            (t / (a ^ 2 + t ^ 2)) * Real.sin (t * x)| := by
    calc
      |(2 : ℝ) *
        ∫ t in (0)..T,
          (t / (a ^ 2 + t ^ 2)) * Real.sin (t * x)|
          =
          |(2 : ℝ)| *
            |∫ t in (0)..T,
              (t / (a ^ 2 + t ^ 2)) * Real.sin (t * x)| := by
            exact abs_mul (2 : ℝ)
              (∫ t in (0)..T,
                (t / (a ^ 2 + t ^ 2)) * Real.sin (t * x))
      _ =
          (2 : ℝ) *
            |∫ t in (0)..T,
              (t / (a ^ 2 + t ^ 2)) * Real.sin (t * x)| := by
            exact congrArg
              (fun r : ℝ =>
                r *
                  |∫ t in (0)..T,
                    (t / (a ^ 2 + t ^ 2)) * Real.sin (t * x)|)
              (abs_of_nonneg htwo_nonneg)
  have hscaled :
      (2 : ℝ) *
        |∫ t in (0)..T,
          (t / (a ^ 2 + t ^ 2)) * Real.sin (t * x)| ≤
        (2 : ℝ) * (1 + (2 : ℝ) * Real.pi) :=
    mul_le_mul_of_nonneg_left hhalf htwo_nonneg
  calc
    |∫ t in Set.Icc (-T) T,
      (t / (a ^ 2 + t ^ 2)) * Real.sin (t * x)|
        =
        |(2 : ℝ) *
          ∫ t in (0)..T,
            (t / (a ^ 2 + t ^ 2)) * Real.sin (t * x)| := by
          exact congrArg abs hsym
    _ =
        (2 : ℝ) *
          |∫ t in (0)..T,
            (t / (a ^ 2 + t ^ 2)) * Real.sin (t * x)| := htwo_abs
    _ ≤ (2 : ℝ) * (1 + (2 : ℝ) * Real.pi) := hscaled

/-- Dirichlet bound for the odd-sine Cauchy component after the standard
scale reduction. -/
theorem scalarFourierLaplacePlemelj_uncompensated_oddSineWindow_scaled_abs_le_two_add_four_pi
    (a : ℝ) (ha : 0 < a) (T x : ℝ) :
    |scalarFourierLaplacePlemelj_uncompensated_oddSineWindow a T x| ≤
      (2 : ℝ) * (1 + (2 : ℝ) * Real.pi) := by
  exact
    scalarFourierLaplacePlemelj_finiteHilbertSineKernel_abs_le_two_add_four_pi
      a ha T x

/-- Fixed-constant Dirichlet bound for the odd-sine component of the
uncompensated Cauchy kernel. -/
theorem scalarFourierLaplacePlemelj_uncompensated_oddSineWindow_abs_le_two_add_four_pi
    (a : ℝ) (ha : 0 < a) (T x : ℝ) :
    |scalarFourierLaplacePlemelj_uncompensated_oddSineWindow a T x| ≤
      (2 : ℝ) * (1 + (2 : ℝ) * Real.pi) := by
  exact
    scalarFourierLaplacePlemelj_uncompensated_oddSineWindow_scaled_abs_le_two_add_four_pi
      a ha T x

/-- Uniform Dirichlet bound for the odd-sine part of the uncompensated Cauchy
Fourier window. -/
theorem scalarFourierLaplacePlemelj_uncompensated_oddSineWindow_uniform_bound
    (a : ℝ) (ha : 0 < a) :
    ∃ C : ℝ,
      0 ≤ C ∧
        ∀ T x : ℝ,
          |scalarFourierLaplacePlemelj_uncompensated_oddSineWindow a T x| ≤ C := by
  exact ⟨(2 : ℝ) * (1 + (2 : ℝ) * Real.pi),
    mul_nonneg zero_le_two
      (add_nonneg zero_le_one (mul_nonneg zero_le_two Real.pi_pos.le)),
    fun T x =>
      scalarFourierLaplacePlemelj_uncompensated_oddSineWindow_abs_le_two_add_four_pi
        a ha T x⟩

/-- Multiplication of two complex numbers presented by real and imaginary
coordinates. -/
theorem scalarFourierLaplacePlemelj_realImag_mul
    (A B C S : ℝ) :
    (((A : ℂ) + ((B : ℝ) : ℂ) * Complex.I) *
        ((C : ℂ) + ((S : ℝ) : ℂ) * Complex.I)) =
      (((A * C - B * S : ℝ) : ℂ) +
        (((A * S + B * C : ℝ) : ℂ) * Complex.I)) := by
  calc
    (((A : ℂ) + ((B : ℝ) : ℂ) * Complex.I) *
        ((C : ℂ) + ((S : ℝ) : ℂ) * Complex.I))
        =
        Complex.mk A B * Complex.mk C S := by
          exact congrArg₂ Mul.mul
            (Complex.mk_eq_add_mul_I A B).symm
            (Complex.mk_eq_add_mul_I C S).symm
    _ = Complex.mk (A * C - B * S) (A * S + B * C) := by
          rfl
    _ =
      (((A * C - B * S : ℝ) : ℂ) +
        (((A * S + B * C : ℝ) : ℂ) * Complex.I)) := by
          exact Complex.mk_eq_add_mul_I (A * C - B * S) (A * S + B * C)

/-- Euler's identity for the real oscillatory factor in the Cauchy Fourier
window. -/
theorem scalarFourierLaplacePlemelj_exp_I_mul_real_eq_cos_add_sin
    (t x : ℝ) :
    Complex.exp (Complex.I * (t : ℂ) * (x : ℂ)) =
      ((Real.cos (t * x) : ℝ) : ℂ) +
        (((Real.sin (t * x) : ℝ) : ℂ) * Complex.I) := by
  have harg :
      Complex.I * (t : ℂ) * (x : ℂ) =
        (((t * x : ℝ) : ℂ) * Complex.I) := by
    calc
      Complex.I * (t : ℂ) * (x : ℂ)
          = Complex.I * ((t : ℂ) * (x : ℂ)) := by
            exact mul_assoc Complex.I (t : ℂ) (x : ℂ)
      _ = ((t : ℂ) * (x : ℂ)) * Complex.I := by
            exact mul_comm Complex.I ((t : ℂ) * (x : ℂ))
      _ = (((t * x : ℝ) : ℂ) * Complex.I) := by
            exact congrArg
              (fun z : ℂ => z * Complex.I)
              (Complex.ofReal_mul t x).symm
  calc
    Complex.exp (Complex.I * (t : ℂ) * (x : ℂ))
        =
        Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) := by
          exact congrArg Complex.exp harg
    _ =
        Complex.cos ((t * x : ℝ) : ℂ) +
          Complex.sin ((t * x : ℝ) : ℂ) * Complex.I := by
          exact Complex.exp_mul_I ((t * x : ℝ) : ℂ)
    _ =
      ((Real.cos (t * x) : ℝ) : ℂ) +
        (((Real.sin (t * x) : ℝ) : ℂ) * Complex.I) := by
          exact congrArg₂ Add.add
            (Complex.ofReal_cos (t * x)).symm
            (congrArg
              (fun z : ℂ => z * Complex.I)
              (Complex.ofReal_sin (t * x)).symm)

/-- Pointwise real/imaginary decomposition of the uncompensated Cauchy Fourier
integrand. -/
theorem scalarFourierLaplacePlemelj_uncompensated_integrand_pointwise_decomposition
    (a : ℝ) (ha : 0 < a) (t x : ℝ) :
    (-1 / ((a : ℂ) + t * Complex.I)) *
        Complex.exp (Complex.I * (t : ℂ) * (x : ℂ)) =
      (((-(a / (a ^ 2 + t ^ 2)) * Real.cos (t * x) -
          (t / (a ^ 2 + t ^ 2)) * Real.sin (t * x) : ℝ) : ℂ) +
        (((-(a / (a ^ 2 + t ^ 2)) * Real.sin (t * x) +
            (t / (a ^ 2 + t ^ 2)) * Real.cos (t * x) : ℝ) : ℂ) *
          Complex.I)) := by
  let A : ℝ := -(a / (a ^ 2 + t ^ 2))
  let B : ℝ := t / (a ^ 2 + t ^ 2)
  let C : ℝ := Real.cos (t * x)
  let S : ℝ := Real.sin (t * x)
  have hkernel :
      (-1 / ((a : ℂ) + t * Complex.I)) =
        ((A : ℝ) : ℂ) + (((B : ℝ) : ℂ) * Complex.I) := by
    calc
      (-1 / ((a : ℂ) + t * Complex.I))
          =
          ((-(a / (a ^ 2 + t ^ 2)) : ℝ) : ℂ) +
            (((t / (a ^ 2 + t ^ 2) : ℝ) : ℂ) * Complex.I) := by
            exact scalarFourierLaplacePlemelj_zero_kernel_pointwise_decomposition
              a ha t
      _ = ((A : ℝ) : ℂ) + (((B : ℝ) : ℂ) * Complex.I) := by
            rfl
  have hexp :
      Complex.exp (Complex.I * (t : ℂ) * (x : ℂ)) =
        ((C : ℝ) : ℂ) + (((S : ℝ) : ℂ) * Complex.I) := by
    calc
      Complex.exp (Complex.I * (t : ℂ) * (x : ℂ))
          =
          ((Real.cos (t * x) : ℝ) : ℂ) +
            (((Real.sin (t * x) : ℝ) : ℂ) * Complex.I) := by
            exact scalarFourierLaplacePlemelj_exp_I_mul_real_eq_cos_add_sin
              t x
      _ = ((C : ℝ) : ℂ) + (((S : ℝ) : ℂ) * Complex.I) := by
            rfl
  have hproduct :
      (((A : ℝ) : ℂ) + (((B : ℝ) : ℂ) * Complex.I)) *
          (((C : ℝ) : ℂ) + (((S : ℝ) : ℂ) * Complex.I)) =
        (((A * C - B * S : ℝ) : ℂ) +
          (((A * S + B * C : ℝ) : ℂ) * Complex.I)) :=
    scalarFourierLaplacePlemelj_realImag_mul A B C S
  calc
    (-1 / ((a : ℂ) + t * Complex.I)) *
        Complex.exp (Complex.I * (t : ℂ) * (x : ℂ))
        =
        (((A : ℝ) : ℂ) + (((B : ℝ) : ℂ) * Complex.I)) *
          Complex.exp (Complex.I * (t : ℂ) * (x : ℂ)) := by
          exact congrArg
            (fun z : ℂ => z * Complex.exp (Complex.I * (t : ℂ) * (x : ℂ)))
            hkernel
    _ =
        (((A : ℝ) : ℂ) + (((B : ℝ) : ℂ) * Complex.I)) *
          (((C : ℝ) : ℂ) + (((S : ℝ) : ℂ) * Complex.I)) := by
          exact congrArg
            (fun z : ℂ =>
              (((A : ℝ) : ℂ) + (((B : ℝ) : ℂ) * Complex.I)) * z)
            hexp
    _ =
        (((A * C - B * S : ℝ) : ℂ) +
          (((A * S + B * C : ℝ) : ℂ) * Complex.I)) := hproduct
    _ =
      (((-(a / (a ^ 2 + t ^ 2)) * Real.cos (t * x) -
          (t / (a ^ 2 + t ^ 2)) * Real.sin (t * x) : ℝ) : ℂ) +
        (((-(a / (a ^ 2 + t ^ 2)) * Real.sin (t * x) +
            (t / (a ^ 2 + t ^ 2)) * Real.cos (t * x) : ℝ) : ℂ) *
          Complex.I)) := by
          rfl

/-- Symmetric interval cancellation for an odd complex-valued function. -/
theorem intervalIntegral_integral_eq_zero_of_forall_neg_eq_neg
    (f : ℝ → ℂ) (T : ℝ) (hodd : ∀ t : ℝ, f (-t) = -f t) :
    ∫ t in (-T)..T, f t = 0 := by
  have hcomp :
      (∫ t in (-T)..T, f (-t)) = ∫ t in (-T)..T, f t := by
    calc
      (∫ t in (-T)..T, f (-t))
          = ∫ t in (-T)..(-(-T)), f t := by
            exact intervalIntegral.integral_comp_neg (f := f) (a := -T) (b := T)
      _ = ∫ t in (-T)..T, f t := by
            exact congrArg
              (fun v : ℝ => ∫ t in (-T)..v, f t)
              (neg_neg T)
  have hneg :
      (∫ t in (-T)..T, f (-t)) = -∫ t in (-T)..T, f t := by
    calc
      (∫ t in (-T)..T, f (-t))
          = ∫ t in (-T)..T, -f t := by
            exact intervalIntegral.integral_congr
              (Filter.Eventually.of_forall hodd)
      _ = -∫ t in (-T)..T, f t := by
            exact intervalIntegral.integral_neg
  have hself_neg : (∫ t in (-T)..T, f t) = -∫ t in (-T)..T, f t :=
    hcomp.symm.trans hneg
  have htwo_zero : (2 : ℂ) * (∫ t in (-T)..T, f t) = 0 := by
    have hsum_zero :
        (∫ t in (-T)..T, f t) + (∫ t in (-T)..T, f t) = 0 := by
      calc
        (∫ t in (-T)..T, f t) + (∫ t in (-T)..T, f t)
            =
            -(∫ t in (-T)..T, f t) + (∫ t in (-T)..T, f t) := by
              exact congrArg
                (fun z : ℂ => z + (∫ t in (-T)..T, f t))
                hself_neg
        _ = 0 := by
            exact neg_add_cancel (∫ t in (-T)..T, f t)
    exact (two_mul (∫ t in (-T)..T, f t)).trans hsum_zero
  exact (mul_eq_zero.mp htwo_zero).resolve_left two_ne_zero

/-- Pointwise oddness of the imaginary remainder in the uncompensated Cauchy
Fourier decomposition. -/
theorem scalarFourierLaplacePlemelj_uncompensated_imaginaryRemainder_pointwise_odd
    (a : ℝ) (ha : 0 < a) (x t : ℝ) :
    (((-(a / (a ^ 2 + (-t) ^ 2)) * Real.sin ((-t) * x) +
        ((-t) / (a ^ 2 + (-t) ^ 2)) * Real.cos ((-t) * x) : ℝ) : ℂ) *
      Complex.I) =
      -((((-(a / (a ^ 2 + t ^ 2)) * Real.sin (t * x) +
          (t / (a ^ 2 + t ^ 2)) * Real.cos (t * x) : ℝ) : ℂ) *
        Complex.I) := by
  let D : ℝ := a ^ 2 + t ^ 2
  let A : ℝ := -(a / D)
  let B : ℝ := t / D
  let S : ℝ := Real.sin (t * x)
  let C : ℝ := Real.cos (t * x)
  have hden : a ^ 2 + (-t) ^ 2 = D := by
    calc
      a ^ 2 + (-t) ^ 2 = a ^ 2 + t ^ 2 := by
        exact congrArg (fun u : ℝ => a ^ 2 + u) (neg_sq t)
      _ = D := by
        rfl
  have hleft_coeff :
      -(a / (a ^ 2 + (-t) ^ 2)) = A := by
    calc
      -(a / (a ^ 2 + (-t) ^ 2)) = -(a / D) := by
        exact congrArg (fun d : ℝ => -(a / d)) hden
      _ = A := by
        rfl
  have hright_coeff :
      (-t) / (a ^ 2 + (-t) ^ 2) = -B := by
    calc
      (-t) / (a ^ 2 + (-t) ^ 2) = (-t) / D := by
        exact congrArg (fun d : ℝ => (-t) / d) hden
      _ = -(t / D) := by
        exact neg_div t D
      _ = -B := by
        rfl
  have hsin :
      Real.sin ((-t) * x) = -S := by
    calc
      Real.sin ((-t) * x) = Real.sin (-(t * x)) := by
        exact congrArg Real.sin (neg_mul t x)
      _ = -Real.sin (t * x) := by
        exact Real.sin_neg (t * x)
      _ = -S := by
        rfl
  have hcos :
      Real.cos ((-t) * x) = C := by
    calc
      Real.cos ((-t) * x) = Real.cos (-(t * x)) := by
        exact congrArg Real.cos (neg_mul t x)
      _ = Real.cos (t * x) := by
        exact Real.cos_neg (t * x)
      _ = C := by
        rfl
  have hreal_left :
      (-(a / (a ^ 2 + (-t) ^ 2)) * Real.sin ((-t) * x) +
          ((-t) / (a ^ 2 + (-t) ^ 2)) * Real.cos ((-t) * x) : ℝ) =
        A * (-S) + (-B) * C := by
    exact congrArg₂ Add.add
      (congrArg₂ Mul.mul hleft_coeff hsin)
      (congrArg₂ Mul.mul hright_coeff hcos)
  have hreal_neg :
      A * (-S) + (-B) * C = -(A * S + B * C) := by
    calc
      A * (-S) + (-B) * C = -(A * S) + (-B) * C := by
        exact congrArg (fun y : ℝ => y + (-B) * C) (mul_neg A S)
      _ = -(A * S) + -(B * C) := by
        exact congrArg (fun y : ℝ => -(A * S) + y) (neg_mul B C)
      _ = -(A * S + B * C) := by
        exact (neg_add (A * S) (B * C)).symm
  have hreal_right :
      (-(a / (a ^ 2 + t ^ 2)) * Real.sin (t * x) +
          (t / (a ^ 2 + t ^ 2)) * Real.cos (t * x) : ℝ) =
        A * S + B * C := by
    rfl
  have hreal :
      (-(a / (a ^ 2 + (-t) ^ 2)) * Real.sin ((-t) * x) +
          ((-t) / (a ^ 2 + (-t) ^ 2)) * Real.cos ((-t) * x) : ℝ) =
        -(-(a / (a ^ 2 + t ^ 2)) * Real.sin (t * x) +
            (t / (a ^ 2 + t ^ 2)) * Real.cos (t * x)) := by
    calc
      (-(a / (a ^ 2 + (-t) ^ 2)) * Real.sin ((-t) * x) +
          ((-t) / (a ^ 2 + (-t) ^ 2)) * Real.cos ((-t) * x) : ℝ)
          = A * (-S) + (-B) * C := hreal_left
      _ = -(A * S + B * C) := hreal_neg
      _ =
          -(-(a / (a ^ 2 + t ^ 2)) * Real.sin (t * x) +
              (t / (a ^ 2 + t ^ 2)) * Real.cos (t * x)) := by
            exact congrArg Neg.neg hreal_right.symm
  calc
    (((-(a / (a ^ 2 + (-t) ^ 2)) * Real.sin ((-t) * x) +
        ((-t) / (a ^ 2 + (-t) ^ 2)) * Real.cos ((-t) * x) : ℝ) : ℂ) *
      Complex.I)
        =
        (((-(-(a / (a ^ 2 + t ^ 2)) * Real.sin (t * x) +
            (t / (a ^ 2 + t ^ 2)) * Real.cos (t * x)) : ℝ) : ℂ) *
          Complex.I) := by
          exact congrArg (fun y : ℝ => ((y : ℂ) * Complex.I)) hreal
    _ =
        (-((( -(a / (a ^ 2 + t ^ 2)) * Real.sin (t * x) +
            (t / (a ^ 2 + t ^ 2)) * Real.cos (t * x) : ℝ) : ℂ))) *
          Complex.I := by
          exact congrArg
            (fun z : ℂ => z * Complex.I)
            (Complex.ofReal_neg
              (-(a / (a ^ 2 + t ^ 2)) * Real.sin (t * x) +
                (t / (a ^ 2 + t ^ 2)) * Real.cos (t * x)))
    _ =
        -((((-(a / (a ^ 2 + t ^ 2)) * Real.sin (t * x) +
            (t / (a ^ 2 + t ^ 2)) * Real.cos (t * x) : ℝ) : ℂ) *
          Complex.I) := by
          exact neg_mul
            (((-(a / (a ^ 2 + t ^ 2)) * Real.sin (t * x) +
              (t / (a ^ 2 + t ^ 2)) * Real.cos (t * x) : ℝ) : ℂ))
            Complex.I

/-- The imaginary remainder in the symmetric uncompensated Cauchy Fourier
window cancels by oddness. -/
theorem scalarFourierLaplacePlemelj_uncompensated_imaginaryRemainder_integral_eq_zero
    (a : ℝ) (ha : 0 < a) (T x : ℝ) :
    ∫ t in Set.Icc (-T) T,
      (((-(a / (a ^ 2 + t ^ 2)) * Real.sin (t * x) +
          (t / (a ^ 2 + t ^ 2)) * Real.cos (t * x) : ℝ) : ℂ) *
        Complex.I) = 0 := by
  let f : ℝ → ℂ :=
    fun t : ℝ =>
      (((-(a / (a ^ 2 + t ^ 2)) * Real.sin (t * x) +
          (t / (a ^ 2 + t ^ 2)) * Real.cos (t * x) : ℝ) : ℂ) *
        Complex.I)
  have hodd : ∀ t : ℝ, f (-t) = -f t := by
    intro t
    unfold f
    exact
      scalarFourierLaplacePlemelj_uncompensated_imaginaryRemainder_pointwise_odd
        a ha x t
  exact intervalIntegral_integral_eq_zero_of_forall_neg_eq_neg f T hodd

/-- Interval integrability of the even-cosine scalar component of the
uncompensated real remainder. -/
theorem scalarFourierLaplacePlemelj_uncompensated_evenCosine_component_intervalIntegrable
    (a : ℝ) (ha : 0 < a) (T x : ℝ) :
    IntervalIntegrable
      (fun t : ℝ =>
        ((-(a / (a ^ 2 + t ^ 2)) * Real.cos (t * x) : ℝ) : ℂ))
      volume (-T) T := by
  have hden_cont : Continuous (fun t : ℝ => a ^ 2 + t ^ 2) :=
    continuous_const.add (continuous_id.pow 2)
  have hden_ne : ∀ t : ℝ, a ^ 2 + t ^ 2 ≠ 0 :=
    scalarFourierLaplacePlemelj_zero_denominator_ne_zero a ha
  have hcoeff :
      Continuous (fun t : ℝ => -(a / (a ^ 2 + t ^ 2))) :=
    (continuous_const.div hden_cont hden_ne).neg
  have htx : Continuous (fun t : ℝ => t * x) :=
    continuous_id.mul continuous_const
  have hcos : Continuous (fun t : ℝ => Real.cos (t * x)) :=
    Real.continuous_cos.comp htx
  have hreal :
      Continuous
        (fun t : ℝ => -(a / (a ^ 2 + t ^ 2)) * Real.cos (t * x)) :=
    hcoeff.mul hcos
  exact (Complex.continuous_ofReal.comp hreal).intervalIntegrable (-T) T

/-- Interval integrability of the odd-sine scalar component of the
uncompensated real remainder. -/
theorem scalarFourierLaplacePlemelj_uncompensated_oddSine_component_intervalIntegrable
    (a : ℝ) (ha : 0 < a) (T x : ℝ) :
    IntervalIntegrable
      (fun t : ℝ =>
        (((t / (a ^ 2 + t ^ 2)) * Real.sin (t * x) : ℝ) : ℂ))
      volume (-T) T := by
  have hden_cont : Continuous (fun t : ℝ => a ^ 2 + t ^ 2) :=
    continuous_const.add (continuous_id.pow 2)
  have hden_ne : ∀ t : ℝ, a ^ 2 + t ^ 2 ≠ 0 :=
    scalarFourierLaplacePlemelj_zero_denominator_ne_zero a ha
  have hcoeff :
      Continuous (fun t : ℝ => t / (a ^ 2 + t ^ 2)) :=
    continuous_id.div hden_cont hden_ne
  have htx : Continuous (fun t : ℝ => t * x) :=
    continuous_id.mul continuous_const
  have hsin : Continuous (fun t : ℝ => Real.sin (t * x)) :=
    Real.continuous_sin.comp htx
  have hreal :
      Continuous
        (fun t : ℝ => (t / (a ^ 2 + t ^ 2)) * Real.sin (t * x)) :=
    hcoeff.mul hsin
  exact (Complex.continuous_ofReal.comp hreal).intervalIntegrable (-T) T

/-- The even-cosine component commutes with the real-to-complex integral. -/
theorem scalarFourierLaplacePlemelj_uncompensated_evenCosine_component_integral_ofReal
    (a T x : ℝ) :
    (∫ t in Set.Icc (-T) T,
      ((-(a / (a ^ 2 + t ^ 2)) * Real.cos (t * x) : ℝ) : ℂ)) =
      ((scalarFourierLaplacePlemelj_uncompensated_evenCosineWindow a T x : ℝ) : ℂ) := by
  calc
    (∫ t in Set.Icc (-T) T,
      ((-(a / (a ^ 2 + t ^ 2)) * Real.cos (t * x) : ℝ) : ℂ))
        =
        ∫ t in (-T)..T,
          ((-(a / (a ^ 2 + t ^ 2)) * Real.cos (t * x) : ℝ) : ℂ) := by
          rfl
    _ =
        ((∫ t in (-T)..T,
          (-(a / (a ^ 2 + t ^ 2)) * Real.cos (t * x) : ℝ)) : ℂ) := by
          exact intervalIntegral.integral_ofReal
    _ =
        ((scalarFourierLaplacePlemelj_uncompensated_evenCosineWindow a T x : ℝ) : ℂ) := by
          rfl

/-- The odd-sine component commutes with the real-to-complex integral. -/
theorem scalarFourierLaplacePlemelj_uncompensated_oddSine_component_integral_ofReal
    (a T x : ℝ) :
    (∫ t in Set.Icc (-T) T,
      (((t / (a ^ 2 + t ^ 2)) * Real.sin (t * x) : ℝ) : ℂ)) =
      ((scalarFourierLaplacePlemelj_uncompensated_oddSineWindow a T x : ℝ) : ℂ) := by
  calc
    (∫ t in Set.Icc (-T) T,
      (((t / (a ^ 2 + t ^ 2)) * Real.sin (t * x) : ℝ) : ℂ))
        =
        ∫ t in (-T)..T,
          (((t / (a ^ 2 + t ^ 2)) * Real.sin (t * x) : ℝ) : ℂ) := by
          rfl
    _ =
        ((∫ t in (-T)..T,
          ((t / (a ^ 2 + t ^ 2)) * Real.sin (t * x) : ℝ)) : ℂ) := by
          exact intervalIntegral.integral_ofReal
    _ =
        ((scalarFourierLaplacePlemelj_uncompensated_oddSineWindow a T x : ℝ) : ℂ) := by
          rfl

/-- The real remainder in the symmetric uncompensated Cauchy Fourier window is
the even-cosine part minus the odd-sine part. -/
theorem scalarFourierLaplacePlemelj_uncompensated_realRemainder_integral_eq_even_sub_odd
    (a : ℝ) (ha : 0 < a) (T x : ℝ) :
    ∫ t in Set.Icc (-T) T,
      ((-(a / (a ^ 2 + t ^ 2)) * Real.cos (t * x) -
          (t / (a ^ 2 + t ^ 2)) * Real.sin (t * x) : ℝ) : ℂ) =
      ((scalarFourierLaplacePlemelj_uncompensated_evenCosineWindow a T x -
        scalarFourierLaplacePlemelj_uncompensated_oddSineWindow a T x : ℝ) : ℂ) := by
  calc
    (∫ t in Set.Icc (-T) T,
      ((-(a / (a ^ 2 + t ^ 2)) * Real.cos (t * x) -
          (t / (a ^ 2 + t ^ 2)) * Real.sin (t * x) : ℝ) : ℂ))
        =
        ∫ t in Set.Icc (-T) T,
          ((-(a / (a ^ 2 + t ^ 2)) * Real.cos (t * x) : ℝ) : ℂ) -
            (((t / (a ^ 2 + t ^ 2)) * Real.sin (t * x) : ℝ) : ℂ) := by
          exact intervalIntegral.integral_congr
            (Filter.Eventually.of_forall
              (fun t : ℝ =>
                Complex.ofReal_sub
                  (-(a / (a ^ 2 + t ^ 2)) * Real.cos (t * x))
                  ((t / (a ^ 2 + t ^ 2)) * Real.sin (t * x))))
    _ =
        (∫ t in Set.Icc (-T) T,
          ((-(a / (a ^ 2 + t ^ 2)) * Real.cos (t * x) : ℝ) : ℂ)) -
          ∫ t in Set.Icc (-T) T,
            (((t / (a ^ 2 + t ^ 2)) * Real.sin (t * x) : ℝ) : ℂ) := by
          exact intervalIntegral.integral_sub
            (scalarFourierLaplacePlemelj_uncompensated_evenCosine_component_intervalIntegrable
              a ha T x)
            (scalarFourierLaplacePlemelj_uncompensated_oddSine_component_intervalIntegrable
              a ha T x)
    _ =
        ((scalarFourierLaplacePlemelj_uncompensated_evenCosineWindow a T x : ℝ) : ℂ) -
          ((scalarFourierLaplacePlemelj_uncompensated_oddSineWindow a T x : ℝ) : ℂ) := by
          exact congrArg₂ Sub.sub
            (scalarFourierLaplacePlemelj_uncompensated_evenCosine_component_integral_ofReal
              a T x)
            (scalarFourierLaplacePlemelj_uncompensated_oddSine_component_integral_ofReal
              a T x)
    _ =
        ((scalarFourierLaplacePlemelj_uncompensated_evenCosineWindow a T x -
          scalarFourierLaplacePlemelj_uncompensated_oddSineWindow a T x : ℝ) : ℂ) := by
          exact
            (Complex.ofReal_sub
              (scalarFourierLaplacePlemelj_uncompensated_evenCosineWindow a T x)
              (scalarFourierLaplacePlemelj_uncompensated_oddSineWindow a T x)).symm

/-- Interval integrability of the real remainder in the uncompensated Cauchy
Fourier decomposition. -/
theorem scalarFourierLaplacePlemelj_uncompensated_realRemainder_intervalIntegrable
    (a : ℝ) (ha : 0 < a) (T x : ℝ) :
    IntervalIntegrable
      (fun t : ℝ =>
        ((-(a / (a ^ 2 + t ^ 2)) * Real.cos (t * x) -
            (t / (a ^ 2 + t ^ 2)) * Real.sin (t * x) : ℝ) : ℂ))
      volume (-T) T := by
  have hden_cont : Continuous (fun t : ℝ => a ^ 2 + t ^ 2) :=
    continuous_const.add (continuous_id.pow 2)
  have hden_ne : ∀ t : ℝ, a ^ 2 + t ^ 2 ≠ 0 :=
    scalarFourierLaplacePlemelj_zero_denominator_ne_zero a ha
  have hleft_coeff :
      Continuous (fun t : ℝ => -(a / (a ^ 2 + t ^ 2))) :=
    (continuous_const.div hden_cont hden_ne).neg
  have hright_coeff :
      Continuous (fun t : ℝ => t / (a ^ 2 + t ^ 2)) :=
    continuous_id.div hden_cont hden_ne
  have htx : Continuous (fun t : ℝ => t * x) :=
    continuous_id.mul continuous_const
  have hcos : Continuous (fun t : ℝ => Real.cos (t * x)) :=
    Real.continuous_cos.comp htx
  have hsin : Continuous (fun t : ℝ => Real.sin (t * x)) :=
    Real.continuous_sin.comp htx
  have hreal :
      Continuous
        (fun t : ℝ =>
          -(a / (a ^ 2 + t ^ 2)) * Real.cos (t * x) -
            (t / (a ^ 2 + t ^ 2)) * Real.sin (t * x)) :=
    (hleft_coeff.mul hcos).sub (hright_coeff.mul hsin)
  exact (Complex.continuous_ofReal.comp hreal).intervalIntegrable (-T) T

/-- Interval integrability of the imaginary remainder in the uncompensated
Cauchy Fourier decomposition. -/
theorem scalarFourierLaplacePlemelj_uncompensated_imaginaryRemainder_intervalIntegrable
    (a : ℝ) (ha : 0 < a) (T x : ℝ) :
    IntervalIntegrable
      (fun t : ℝ =>
        (((-(a / (a ^ 2 + t ^ 2)) * Real.sin (t * x) +
            (t / (a ^ 2 + t ^ 2)) * Real.cos (t * x) : ℝ) : ℂ) *
          Complex.I))
      volume (-T) T := by
  have hden_cont : Continuous (fun t : ℝ => a ^ 2 + t ^ 2) :=
    continuous_const.add (continuous_id.pow 2)
  have hden_ne : ∀ t : ℝ, a ^ 2 + t ^ 2 ≠ 0 :=
    scalarFourierLaplacePlemelj_zero_denominator_ne_zero a ha
  have hleft_coeff :
      Continuous (fun t : ℝ => -(a / (a ^ 2 + t ^ 2))) :=
    (continuous_const.div hden_cont hden_ne).neg
  have hright_coeff :
      Continuous (fun t : ℝ => t / (a ^ 2 + t ^ 2)) :=
    continuous_id.div hden_cont hden_ne
  have htx : Continuous (fun t : ℝ => t * x) :=
    continuous_id.mul continuous_const
  have hcos : Continuous (fun t : ℝ => Real.cos (t * x)) :=
    Real.continuous_cos.comp htx
  have hsin : Continuous (fun t : ℝ => Real.sin (t * x)) :=
    Real.continuous_sin.comp htx
  have hreal :
      Continuous
        (fun t : ℝ =>
          -(a / (a ^ 2 + t ^ 2)) * Real.sin (t * x) +
            (t / (a ^ 2 + t ^ 2)) * Real.cos (t * x)) :=
    (hleft_coeff.mul hsin).add (hright_coeff.mul hcos)
  exact
    ((Complex.continuous_ofReal.comp hreal).mul continuous_const).intervalIntegrable
      (-T) T

/-- Additivity of the real and imaginary remainders in the uncompensated
Cauchy Fourier decomposition on a finite symmetric window. -/
theorem scalarFourierLaplacePlemelj_uncompensated_remainder_integral_add
    (a : ℝ) (ha : 0 < a) (T x : ℝ) :
    ∫ t in Set.Icc (-T) T,
      (((-(a / (a ^ 2 + t ^ 2)) * Real.cos (t * x) -
          (t / (a ^ 2 + t ^ 2)) * Real.sin (t * x) : ℝ) : ℂ) +
        (((-(a / (a ^ 2 + t ^ 2)) * Real.sin (t * x) +
            (t / (a ^ 2 + t ^ 2)) * Real.cos (t * x) : ℝ) : ℂ) *
          Complex.I)) =
      (∫ t in Set.Icc (-T) T,
        ((-(a / (a ^ 2 + t ^ 2)) * Real.cos (t * x) -
            (t / (a ^ 2 + t ^ 2)) * Real.sin (t * x) : ℝ) : ℂ)) +
        ∫ t in Set.Icc (-T) T,
          (((-(a / (a ^ 2 + t ^ 2)) * Real.sin (t * x) +
              (t / (a ^ 2 + t ^ 2)) * Real.cos (t * x) : ℝ) : ℂ) *
            Complex.I) := by
  exact intervalIntegral.integral_add
    (scalarFourierLaplacePlemelj_uncompensated_realRemainder_intervalIntegrable
      a ha T x)
    (scalarFourierLaplacePlemelj_uncompensated_imaginaryRemainder_intervalIntegrable
      a ha T x)

/-- Exact real decomposition of the uncompensated symmetric Cauchy Fourier
window into its surviving even-cosine and odd-sine pieces. -/
theorem scalarFourierLaplacePlemelj_uncompensated_window_eq_evenCosine_sub_oddSine
    (a : ℝ) (ha : 0 < a) (T x : ℝ) :
    (∫ t in Set.Icc (-T) T,
      (-1 / ((a : ℂ) + t * Complex.I)) *
        Complex.exp
          (Complex.I * (t : ℂ) * (x : ℂ))) =
      ((scalarFourierLaplacePlemelj_uncompensated_evenCosineWindow a T x -
        scalarFourierLaplacePlemelj_uncompensated_oddSineWindow a T x : ℝ) : ℂ) := by
  calc
    (∫ t in Set.Icc (-T) T,
      (-1 / ((a : ℂ) + t * Complex.I)) *
        Complex.exp
          (Complex.I * (t : ℂ) * (x : ℂ))) =
        ∫ t in Set.Icc (-T) T,
          (((-(a / (a ^ 2 + t ^ 2)) * Real.cos (t * x) -
              (t / (a ^ 2 + t ^ 2)) * Real.sin (t * x) : ℝ) : ℂ) +
            (((-(a / (a ^ 2 + t ^ 2)) * Real.sin (t * x) +
                (t / (a ^ 2 + t ^ 2)) * Real.cos (t * x) : ℝ) : ℂ) *
              Complex.I)) := by
          exact intervalIntegral.integral_congr
            (Filter.Eventually.of_forall
              (fun t : ℝ =>
                scalarFourierLaplacePlemelj_uncompensated_integrand_pointwise_decomposition
                  a ha t x))
    _ =
        (∫ t in Set.Icc (-T) T,
          ((-(a / (a ^ 2 + t ^ 2)) * Real.cos (t * x) -
              (t / (a ^ 2 + t ^ 2)) * Real.sin (t * x) : ℝ) : ℂ)) +
          ∫ t in Set.Icc (-T) T,
            (((-(a / (a ^ 2 + t ^ 2)) * Real.sin (t * x) +
                (t / (a ^ 2 + t ^ 2)) * Real.cos (t * x) : ℝ) : ℂ) *
              Complex.I) := by
          exact
            scalarFourierLaplacePlemelj_uncompensated_remainder_integral_add
              a ha T x
    _ =
        (∫ t in Set.Icc (-T) T,
          ((-(a / (a ^ 2 + t ^ 2)) * Real.cos (t * x) -
              (t / (a ^ 2 + t ^ 2)) * Real.sin (t * x) : ℝ) : ℂ)) + 0 := by
          exact congrArg
            (fun z : ℂ =>
              (∫ t in Set.Icc (-T) T,
                ((-(a / (a ^ 2 + t ^ 2)) * Real.cos (t * x) -
                    (t / (a ^ 2 + t ^ 2)) * Real.sin (t * x) : ℝ) : ℂ)) + z)
            (scalarFourierLaplacePlemelj_uncompensated_imaginaryRemainder_integral_eq_zero
              a ha T x)
    _ =
        ∫ t in Set.Icc (-T) T,
          ((-(a / (a ^ 2 + t ^ 2)) * Real.cos (t * x) -
              (t / (a ^ 2 + t ^ 2)) * Real.sin (t * x) : ℝ) : ℂ) := by
          exact add_zero _
    _ =
      ((scalarFourierLaplacePlemelj_uncompensated_evenCosineWindow a T x -
        scalarFourierLaplacePlemelj_uncompensated_oddSineWindow a T x : ℝ) : ℂ) := by
          exact
            scalarFourierLaplacePlemelj_uncompensated_realRemainder_integral_eq_even_sub_odd
              a ha T x

/-- Assembly of the uncompensated complex Cauchy window norm from the bounded
even-cosine and odd-sine real components. -/
theorem scalarFourierLaplacePlemelj_uncompensated_window_norm_bound_of_even_odd
    (a : ℝ) (ha : 0 < a) (T x Ceven Codd : ℝ)
    (heven :
      |scalarFourierLaplacePlemelj_uncompensated_evenCosineWindow a T x| ≤ Ceven)
    (hodd :
      |scalarFourierLaplacePlemelj_uncompensated_oddSineWindow a T x| ≤ Codd) :
    ‖∫ t in Set.Icc (-T) T,
      (-1 / ((a : ℂ) + t * Complex.I)) *
        Complex.exp
          (Complex.I * (t : ℂ) * (x : ℂ))‖ ≤ Ceven + Codd := by
  let E : ℝ := scalarFourierLaplacePlemelj_uncompensated_evenCosineWindow a T x
  let O : ℝ := scalarFourierLaplacePlemelj_uncompensated_oddSineWindow a T x
  have hdecomp :
      (∫ t in Set.Icc (-T) T,
        (-1 / ((a : ℂ) + t * Complex.I)) *
          Complex.exp
            (Complex.I * (t : ℂ) * (x : ℂ))) =
        ((E - O : ℝ) : ℂ) := by
    exact
      scalarFourierLaplacePlemelj_uncompensated_window_eq_evenCosine_sub_oddSine
        a ha T x
  have hnorm :
      ‖((E - O : ℝ) : ℂ)‖ = |E - O| :=
    RCLike.norm_ofReal (K := ℂ) (E - O)
  have htri : |E - O| ≤ |E| + |O| :=
    abs_sub_le E O
  have heven' : |E| ≤ Ceven := by
    unfold E
    exact heven
  have hodd' : |O| ≤ Codd := by
    unfold O
    exact hodd
  calc
    ‖∫ t in Set.Icc (-T) T,
      (-1 / ((a : ℂ) + t * Complex.I)) *
        Complex.exp
          (Complex.I * (t : ℂ) * (x : ℂ))‖ =
        ‖((E - O : ℝ) : ℂ)‖ := by
      exact congrArg norm hdecomp
    _ = |E - O| := hnorm
    _ ≤ |E| + |O| := htri
    _ ≤ Ceven + Codd := by
      exact add_le_add heven' hodd'

/-- Dirichlet decomposition bound for the uncompensated scalar Cauchy Fourier
window.

This is the real-variable core of the near-jump Cauchy estimate: after splitting
`1 / (a + i t)` into its even real and odd imaginary pieces, Dirichlet's
oscillatory-integral bound controls the finite symmetric windows uniformly in
both the radius and frequency. -/
theorem scalarFourierLaplacePlemelj_uncompensated_window_dirichletDecomposition_uniform_norm_bound
    (a : ℝ) (ha : 0 < a) :
    ∃ C : ℝ,
      0 ≤ C ∧
        ∀ T x : ℝ,
          ‖∫ t in Set.Icc (-T) T,
            (-1 / ((a : ℂ) + t * Complex.I)) *
              Complex.exp
                (Complex.I * (t : ℂ) * (x : ℂ))‖
          ≤ C := by
  match scalarFourierLaplacePlemelj_uncompensated_evenCosineWindow_uniform_bound
    a ha with
  | ⟨Ceven, hCeven_nonneg, heven⟩ =>
      match scalarFourierLaplacePlemelj_uncompensated_oddSineWindow_uniform_bound
        a ha with
      | ⟨Codd, hCodd_nonneg, hodd⟩ =>
          let C : ℝ := Ceven + Codd
          have hC_nonneg : 0 ≤ C := by
            unfold C
            exact add_nonneg hCeven_nonneg hCodd_nonneg
          exact
            ⟨C, hC_nonneg,
              fun T x =>
                scalarFourierLaplacePlemelj_uncompensated_window_norm_bound_of_even_odd
                  a ha T x Ceven Codd (heven T x) (hodd T x)⟩

/-- Global uniform bound for the uncompensated scalar Cauchy Fourier window. -/
theorem scalarFourierLaplacePlemelj_uncompensated_window_uniform_norm_bound
    (a : ℝ) (ha : 0 < a) :
    ∃ C : ℝ,
      0 ≤ C ∧
        ∀ T x : ℝ,
          ‖∫ t in Set.Icc (-T) T,
            (-1 / ((a : ℂ) + t * Complex.I)) *
              Complex.exp
                (Complex.I * (t : ℂ) * (x : ℂ))‖
          ≤ C := by
  exact
    scalarFourierLaplacePlemelj_uncompensated_window_dirichletDecomposition_uniform_norm_bound
      a ha

/-- Uncompensated symmetric Cauchy-window bound in a punctured neighborhood of
the Plemelj jump. -/
theorem scalarFourierLaplacePlemelj_uncompensated_punctured_nearZero_norm_bound_eventually
    (a : ℝ) (ha : 0 < a) (R δ : ℝ) (hδ : 0 < δ) :
    ∃ C : ℝ,
      0 ≤ C ∧
        ∀ᶠ T in atTop,
          ∀ x : ℝ,
            x ≠ 0 →
            ‖x‖ < δ →
            ‖x‖ ≤ R →
              ‖∫ t in Set.Icc (-T) T,
                (-1 / ((a : ℂ) + t * Complex.I)) *
                  Complex.exp
                    (Complex.I * (t : ℂ) * (x : ℂ))‖
              ≤ C := by
  match
    scalarFourierLaplacePlemelj_uncompensated_window_uniform_norm_bound
      a ha
  with
  | ⟨C, hC_nonneg, hC⟩ =>
      exact
        ⟨C, hC_nonneg,
          Eventually.of_forall
            (fun T x _hx_ne _hxδ _hxR =>
              hC T x)⟩

/-- Uniform punctured-neighborhood Cauchy-window estimate near the Plemelj
jump.  This is the shared near-zero Dirichlet estimate used by both signs. -/
theorem scalarFourierLaplacePlemelj_compactInterval_punctured_nearZero_norm_bound_eventually
    (a : ℝ) (ha : 0 < a) (R δ : ℝ) (hδ : 0 < δ) :
    ∃ C : ℝ,
      0 ≤ C ∧
        ∀ᶠ T in atTop,
          ∀ x : ℝ,
            x ≠ 0 →
            ‖x‖ < δ →
            ‖x‖ ≤ R →
              ‖(∫ t in Set.Icc (-T) T,
                (-1 / ((a : ℂ) + t * Complex.I)) *
                  Complex.exp
                    (Complex.I * (t : ℂ) * (x : ℂ)) *
                  Complex.exp ((a : ℂ) * (x : ℂ)))‖
              ≤ C := by
  match
    scalarFourierLaplacePlemelj_uncompensated_punctured_nearZero_norm_bound_eventually
      a ha R δ hδ
  with
  | ⟨Craw, hCraw_nonneg, hraw⟩ =>
      let Ebound : ℝ := Real.exp (a * R)
      let C : ℝ := Craw * Ebound
      have hEbound_nonneg : 0 ≤ Ebound := by
        unfold Ebound
        exact (Real.exp_pos (a * R)).le
      have hC_nonneg : 0 ≤ C := by
        unfold C
        exact mul_nonneg hCraw_nonneg hEbound_nonneg
      exact
        ⟨C, hC_nonneg,
          hraw.mono
            (fun T hT x hx_ne hxδ hxR =>
              let W : ℂ :=
                ∫ t in Set.Icc (-T) T,
                  (-1 / ((a : ℂ) + t * Complex.I)) *
                    Complex.exp
                      (Complex.I * (t : ℂ) * (x : ℂ))
              let E : ℂ := Complex.exp ((a : ℂ) * (x : ℂ))
              have htarget :
                  (∫ t in Set.Icc (-T) T,
                    (-1 / ((a : ℂ) + t * Complex.I)) *
                      Complex.exp
                        (Complex.I * (t : ℂ) * (x : ℂ)) *
                      Complex.exp ((a : ℂ) * (x : ℂ))) =
                  W * E :=
                (scalarFourierLaplacePlemelj_positive_window_mul_exp_eq_window_with_exp
                  a x T).symm
              have hE_le : ‖E‖ ≤ Ebound := by
                unfold E
                unfold Ebound
                exact
                  scalarFourierLaplacePlemelj_positive_exp_norm_le_intervalEndpoint
                    a ha R x hxR
              have hE_nonneg : 0 ≤ ‖E‖ :=
                norm_nonneg E
              have hmul :
                  ‖W‖ * ‖E‖ ≤ Craw * Ebound :=
                mul_le_mul (hT x hx_ne hxδ hxR) hE_le hE_nonneg hCraw_nonneg
              calc
                ‖(∫ t in Set.Icc (-T) T,
                  (-1 / ((a : ℂ) + t * Complex.I)) *
                    Complex.exp
                      (Complex.I * (t : ℂ) * (x : ℂ)) *
                    Complex.exp ((a : ℂ) * (x : ℂ)))‖
                    = ‖W * E‖ := by
                  exact congrArg norm htarget
                _ = ‖W‖ * ‖E‖ := by
                  exact norm_mul W E
                _ ≤ Craw * Ebound := hmul
                _ = C := by
                  rfl)⟩

/-- Positive-time near-zero compact-interval estimate for the normalized
scalar Fourier-Laplace Plemelj kernel. -/
theorem scalarFourierLaplacePlemelj_compactInterval_positive_nearZero_norm_bound_eventually
    (a : ℝ) (ha : 0 < a) (R δ : ℝ) (hδ : 0 < δ) :
    ∃ C : ℝ,
      0 ≤ C ∧
        ∀ᶠ T in atTop,
          ∀ x : ℝ,
            0 < x →
            x < δ →
            ‖x‖ ≤ R →
              ‖(∫ t in Set.Icc (-T) T,
                (-1 / ((a : ℂ) + t * Complex.I)) *
                  Complex.exp
                    (Complex.I * (t : ℂ) * (x : ℂ)) *
                  Complex.exp ((a : ℂ) * (x : ℂ)))‖
              ≤ C := by
  match
    scalarFourierLaplacePlemelj_compactInterval_punctured_nearZero_norm_bound_eventually
      a ha R δ hδ
  with
  | ⟨C, hC_nonneg, hnear⟩ =>
      exact
        ⟨C, hC_nonneg,
          hnear.mono
            (fun T hT x hxpos hxδ hxR =>
              have hnorm : ‖x‖ = x := by
                exact (Real.norm_eq_abs x).trans (abs_of_pos hxpos)
              have hnorm_lt : ‖x‖ < δ :=
                hnorm.trans_lt hxδ
              hT x (ne_of_gt hxpos) hnorm_lt hxR)⟩

/-- Assembly of the positive compact-interval estimate from its near-zero and
away-from-zero pieces. -/
theorem scalarFourierLaplacePlemelj_compactInterval_positive_norm_bound_eventually_of_split
    (a : ℝ) (ha : 0 < a) (R δ Cnear Caway : ℝ) (hδ : 0 < δ)
    (hCnear_nonneg : 0 ≤ Cnear) (hCaway_nonneg : 0 ≤ Caway)
    (hnear :
      ∀ᶠ T in atTop,
        ∀ x : ℝ,
          0 < x →
          x < δ →
          ‖x‖ ≤ R →
            ‖(∫ t in Set.Icc (-T) T,
              (-1 / ((a : ℂ) + t * Complex.I)) *
                Complex.exp
                  (Complex.I * (t : ℂ) * (x : ℂ)) *
                Complex.exp ((a : ℂ) * (x : ℂ)))‖
            ≤ Cnear)
    (haway :
      ∀ᶠ T in atTop,
        ∀ x : ℝ,
          δ ≤ x →
          ‖x‖ ≤ R →
            ‖(∫ t in Set.Icc (-T) T,
              (-1 / ((a : ℂ) + t * Complex.I)) *
                Complex.exp
                  (Complex.I * (t : ℂ) * (x : ℂ)) *
                Complex.exp ((a : ℂ) * (x : ℂ)))‖
            ≤ Caway) :
    ∃ C : ℝ,
      0 ≤ C ∧
        ∀ᶠ T in atTop,
          ∀ x : ℝ,
            0 < x →
            ‖x‖ ≤ R →
              ‖(∫ t in Set.Icc (-T) T,
                (-1 / ((a : ℂ) + t * Complex.I)) *
                  Complex.exp
                    (Complex.I * (t : ℂ) * (x : ℂ)) *
                  Complex.exp ((a : ℂ) * (x : ℂ)))‖
              ≤ C := by
  let C : ℝ := max Cnear Caway
  have hC_nonneg : 0 ≤ C := by
    unfold C
    exact hCnear_nonneg.trans (le_max_left Cnear Caway)
  have hnear_le : Cnear ≤ C := by
    unfold C
    exact le_max_left Cnear Caway
  have haway_le : Caway ≤ C := by
    unfold C
    exact le_max_right Cnear Caway
  exact
    ⟨C, hC_nonneg,
      hnear.and haway |>.mono
        (fun T hsplit =>
          fun x hxpos hxR =>
            match lt_or_ge x δ with
            | Or.inl hx_lt_delta =>
                (hsplit.1 x hxpos hx_lt_delta hxR).trans hnear_le
            | Or.inr hx_ge_delta =>
                (hsplit.2 x hx_ge_delta hxR).trans haway_le)⟩

theorem scalarFourierLaplacePlemelj_compactInterval_positive_norm_bound_eventually
    (a : ℝ) (ha : 0 < a) (R : ℝ) :
    ∃ C : ℝ,
      0 ≤ C ∧
        ∀ᶠ T in atTop,
          ∀ x : ℝ,
            0 < x →
            ‖x‖ ≤ R →
              ‖(∫ t in Set.Icc (-T) T,
                (-1 / ((a : ℂ) + t * Complex.I)) *
                  Complex.exp
                    (Complex.I * (t : ℂ) * (x : ℂ)) *
                  Complex.exp ((a : ℂ) * (x : ℂ)))‖
              ≤ C := by
  let δ : ℝ := 1
  have hδ : 0 < δ := by
    unfold δ
    exact zero_lt_one
  match scalarFourierLaplacePlemelj_compactInterval_positive_nearZero_norm_bound_eventually
    a ha R δ hδ with
  | ⟨Cnear, hCnear_nonneg, hnear⟩ =>
      match scalarFourierLaplacePlemelj_compactInterval_positive_awayZero_norm_bound_eventually
        a ha R δ hδ with
      | ⟨Caway, hCaway_nonneg, haway⟩ =>
          exact
            scalarFourierLaplacePlemelj_compactInterval_positive_norm_bound_eventually_of_split
              a ha R δ Cnear Caway hδ hCnear_nonneg hCaway_nonneg
              hnear haway

/-- Reciprocal factor in the negative away-zero Jordan majorant is bounded by
the away-from-zero threshold. -/
theorem scalarFourierLaplacePlemelj_negative_awayZero_reciprocal_le
    (T x δ : ℝ) (hT : 0 < T) (hδ : 0 < δ) (hxδ : x ≤ -δ) :
    (T * (-x))⁻¹ ≤ (T * δ)⁻¹ := by
  have hδ_negx : δ ≤ -x := by
    calc
      δ = -(-δ) := by
        exact (neg_neg δ).symm
      _ ≤ -x := by
        exact neg_le_neg hxδ
  have hTδ_pos : 0 < T * δ :=
    mul_pos hT hδ
  have hTδ_le_Tnegx : T * δ ≤ T * (-x) :=
    mul_le_mul_of_nonneg_left hδ_negx hT.le
  exact inv_anti₀ hTδ_pos hTδ_le_Tnegx

/-- Product assembly for the negative lower-arc Jordan majorant away from
zero. -/
theorem scalarFourierLaplacePlemelj_negativeLowerArcJordanMajorant_awayZero_mulExp_bound_eventually_of_factors
    (a : ℝ) (ha : 0 < a) (R δ B : ℝ) (hδ : 0 < δ)
    (hB_nonneg : 0 ≤ B)
    (hpref :
      ∀ᶠ T in atTop,
        Real.pi * T / (T - a) ≤ B) :
    ∃ C : ℝ,
      0 ≤ C ∧
        ∀ᶠ T in atTop,
          ∀ x : ℝ,
            x ≤ -δ →
            ‖x‖ ≤ R →
              scalarFourierLaplacePlemelj_negativeLowerArcJordanMajorant a x T *
                ‖Complex.exp ((a : ℂ) * (x : ℂ))‖ ≤ C := by
  let C : ℝ := B * δ⁻¹ * Real.exp (a * R)
  have hδ_inv_nonneg : 0 ≤ δ⁻¹ :=
    inv_nonneg_of_nonneg hδ.le
  have hexp_nonneg : 0 ≤ Real.exp (a * R) :=
    (Real.exp_pos (a * R)).le
  have hC_nonneg : 0 ≤ C := by
    unfold C
    exact mul_nonneg (mul_nonneg hB_nonneg hδ_inv_nonneg) hexp_nonneg
  exact
    ⟨C, hC_nonneg,
      (hpref.and (eventually_gt_atTop (max a 1))).mono
        (fun T hTpair =>
          fun x hxδ hxR =>
            let Pref : ℝ := Real.pi * T / (T - a)
            let Rec : ℝ := (T * (-x))⁻¹
            let E : ℝ := ‖Complex.exp ((a : ℂ) * (x : ℂ))‖
            have hpref_le : Pref ≤ B := hTpair.1
            have hmax : max a 1 < T := hTpair.2
            have haT : a < T := (le_max_left a 1).trans_lt hmax
            have h_one_lt_T : 1 < T := (le_max_right a 1).trans_lt hmax
            have hT_pos : 0 < T := zero_lt_one.trans h_one_lt_T
            have hden_pos : 0 < T - a := sub_pos.mpr haT
            have hpref_nonneg : 0 ≤ Pref := by
              unfold Pref
              exact div_nonneg
                (mul_nonneg Real.pi_nonneg hT_pos.le)
                hden_pos.le
            have hrec_le_Tδ :
                Rec ≤ (T * δ)⁻¹ := by
              unfold Rec
              exact
                scalarFourierLaplacePlemelj_negative_awayZero_reciprocal_le
                  T x δ hT_pos hδ hxδ
            have hδ_le_Tδ : δ ≤ T * δ := by
              calc
                δ = 1 * δ := by
                  exact (one_mul δ).symm
                _ ≤ T * δ := by
                  exact mul_le_mul_of_nonneg_right h_one_lt_T.le hδ.le
            have hTδ_inv_le : (T * δ)⁻¹ ≤ δ⁻¹ :=
              inv_anti₀ hδ hδ_le_Tδ
            have hrec_le : Rec ≤ δ⁻¹ :=
              hrec_le_Tδ.trans hTδ_inv_le
            have hδ_negx_nonneg : 0 ≤ -x := by
              have hδ_le_negx : δ ≤ -x := by
                calc
                  δ = -(-δ) := by
                    exact (neg_neg δ).symm
                  _ ≤ -x := by
                    exact neg_le_neg hxδ
              exact hδ.le.trans hδ_le_negx
            have hrec_nonneg : 0 ≤ Rec := by
              unfold Rec
              exact inv_nonneg_of_nonneg
                (mul_nonneg hT_pos.le hδ_negx_nonneg)
            have hE_le : E ≤ Real.exp (a * R) := by
              unfold E
              exact
                scalarFourierLaplacePlemelj_positive_exp_norm_le_intervalEndpoint
                  a ha R x hxR
            have hE_nonneg : 0 ≤ E := by
              unfold E
              exact norm_nonneg _
            have h_pref_rec :
                Pref * Rec ≤ B * δ⁻¹ :=
              mul_le_mul hpref_le hrec_le hrec_nonneg hB_nonneg
            have h_product :
                (Pref * Rec) * E ≤ (B * δ⁻¹) * Real.exp (a * R) :=
              mul_le_mul h_pref_rec hE_le hE_nonneg
                (mul_nonneg hB_nonneg hδ_inv_nonneg)
            calc
              scalarFourierLaplacePlemelj_negativeLowerArcJordanMajorant a x T *
                  ‖Complex.exp ((a : ℂ) * (x : ℂ))‖ =
                  (Pref * Rec) * E := by
                rfl
              _ ≤ (B * δ⁻¹) * Real.exp (a * R) := h_product
              _ = C := by
                rfl)⟩

theorem scalarFourierLaplacePlemelj_negativeLowerArcJordanMajorant_awayZero_mulExp_bound_eventually
    (a : ℝ) (ha : 0 < a) (R δ : ℝ) (hδ : 0 < δ) :
    ∃ C : ℝ,
      0 ≤ C ∧
        ∀ᶠ T in atTop,
          ∀ x : ℝ,
            x ≤ -δ →
            ‖x‖ ≤ R →
              scalarFourierLaplacePlemelj_negativeLowerArcJordanMajorant a x T *
                ‖Complex.exp ((a : ℂ) * (x : ℂ))‖ ≤ C := by
  let B : ℝ := Real.pi + 1
  have hB_nonneg : 0 ≤ B := by
    unfold B
    exact add_nonneg Real.pi_nonneg zero_le_one
  exact
    scalarFourierLaplacePlemelj_negativeLowerArcJordanMajorant_awayZero_mulExp_bound_eventually_of_factors
      a ha R δ B hδ hB_nonneg
      (scalarFourierLaplacePlemelj_positiveUpperArcJordanPrefactor_eventually_le
        a)

/-- Negative lower-arc away-from-zero estimate from its Jordan majorant. -/
theorem scalarFourierLaplacePlemelj_negativeLowerArc_awayZero_mulExp_norm_bound_eventually_of_jordan
    (a : ℝ) (ha : 0 < a) (R δ Cj : ℝ) (hδ : 0 < δ)
    (hCj_nonneg : 0 ≤ Cj)
    (hjordan :
      ∀ᶠ T in atTop,
        ∀ x : ℝ,
          x ≤ -δ →
          ‖x‖ ≤ R →
            scalarFourierLaplacePlemelj_negativeLowerArcJordanMajorant a x T *
              ‖Complex.exp ((a : ℂ) * (x : ℂ))‖ ≤ Cj) :
    ∃ C : ℝ,
      0 ≤ C ∧
        ∀ᶠ T in atTop,
          ∀ x : ℝ,
            x ≤ -δ →
            ‖x‖ ≤ R →
              ‖scalarFourierLaplacePlemelj_negativeLowerArc a x T *
                Complex.exp ((a : ℂ) * (x : ℂ))‖ ≤ C := by
  exact
    ⟨Cj, hCj_nonneg,
      (hjordan.and (eventually_gt_atTop a)).mono
        (fun T hTpair =>
          fun x hxδ hxR =>
            have hxneg : x < 0 := by
              have hnegδ_neg : -δ < 0 := neg_lt_zero.mpr hδ
              exact hxδ.trans_lt hnegδ_neg
            have harc :
                ‖scalarFourierLaplacePlemelj_negativeLowerArc a x T‖ ≤
                  scalarFourierLaplacePlemelj_negativeLowerArcJordanMajorant a x T :=
              (scalarFourierLaplacePlemelj_negativeLowerArc_norm_le_jordanDensity_integral
                a ha x hxneg T hTpair.2).trans
                (scalarFourierLaplacePlemelj_negativeLowerArcJordanDensity_integral_le_majorant
                  a ha x hxneg T hTpair.2)
            have hexp_nonneg :
                0 ≤ ‖Complex.exp ((a : ℂ) * (x : ℂ))‖ :=
              norm_nonneg _
            calc
              ‖scalarFourierLaplacePlemelj_negativeLowerArc a x T *
                  Complex.exp ((a : ℂ) * (x : ℂ))‖ =
                  ‖scalarFourierLaplacePlemelj_negativeLowerArc a x T‖ *
                    ‖Complex.exp ((a : ℂ) * (x : ℂ))‖ := by
                exact norm_mul
                  (scalarFourierLaplacePlemelj_negativeLowerArc a x T)
                  (Complex.exp ((a : ℂ) * (x : ℂ)))
              _ ≤
                  scalarFourierLaplacePlemelj_negativeLowerArcJordanMajorant a x T *
                    ‖Complex.exp ((a : ℂ) * (x : ℂ))‖ := by
                exact mul_le_mul_of_nonneg_right harc hexp_nonneg
              _ ≤ Cj := hTpair.1 x hxδ hxR)⟩

theorem scalarFourierLaplacePlemelj_negativeLowerArc_awayZero_mulExp_norm_bound_eventually
    (a : ℝ) (ha : 0 < a) (R δ : ℝ) (hδ : 0 < δ) :
    ∃ C : ℝ,
      0 ≤ C ∧
        ∀ᶠ T in atTop,
          ∀ x : ℝ,
            x ≤ -δ →
            ‖x‖ ≤ R →
              ‖scalarFourierLaplacePlemelj_negativeLowerArc a x T *
                Complex.exp ((a : ℂ) * (x : ℂ))‖ ≤ C := by
  match
    scalarFourierLaplacePlemelj_negativeLowerArcJordanMajorant_awayZero_mulExp_bound_eventually
      a ha R δ hδ
  with
  | ⟨Cj, hCj_nonneg, hjordan⟩ =>
      exact
        scalarFourierLaplacePlemelj_negativeLowerArc_awayZero_mulExp_norm_bound_eventually_of_jordan
          a ha R δ Cj hδ hCj_nonneg hjordan

/-- Radius-qualified finite lower-half-plane pole-free identity for the
negative-time scalar window. -/
theorem scalarFourierLaplacePlemelj_negative_window_add_lowerArc_eq_zero_of_radius
    (a : ℝ) (ha : 0 < a) (x : ℝ) (hx : x < 0)
    (T : ℝ) (hT : 0 < T) :
      (∫ t in Set.Icc (-T) T,
        (-1 / ((a : ℂ) + t * Complex.I)) *
          Complex.exp
            (Complex.I * (t : ℂ) * (x : ℂ))) +
          scalarFourierLaplacePlemelj_negativeLowerArc a x T =
        0 := by
  have hclosed :
      scalarFourierLaplacePlemelj_negativeClosedContour a x T = 0 :=
    scalarFourierLaplacePlemelj_negativeClosedContour_eq_zero_of_poleOutside
      a ha x hx T hT
  exact
    (scalarFourierLaplacePlemelj_negativeClosedContour_eq_window_add_lowerArc
      a x T).symm.trans hclosed

/-- Exact radius-qualified negative finite-window formula after moving the
compensating exponential inside the window. -/
theorem scalarFourierLaplacePlemelj_negative_window_with_exp_eq_neg_lowerArc_mul_exp_of_radius
    (a : ℝ) (ha : 0 < a) (x : ℝ) (hx : x < 0)
    (T : ℝ) (hT : 0 < T) :
      (∫ t in Set.Icc (-T) T,
        (-1 / ((a : ℂ) + t * Complex.I)) *
          Complex.exp
            (Complex.I * (t : ℂ) * (x : ℂ)) *
          Complex.exp ((a : ℂ) * (x : ℂ))) =
      -(scalarFourierLaplacePlemelj_negativeLowerArc a x T *
          Complex.exp ((a : ℂ) * (x : ℂ))) := by
  let W : ℂ :=
    ∫ t in Set.Icc (-T) T,
      (-1 / ((a : ℂ) + t * Complex.I)) *
        Complex.exp
          (Complex.I * (t : ℂ) * (x : ℂ))
  let A : ℂ := scalarFourierLaplacePlemelj_negativeLowerArc a x T
  let E : ℂ := Complex.exp ((a : ℂ) * (x : ℂ))
  have hadd : W + A = 0 :=
    scalarFourierLaplacePlemelj_negative_window_add_lowerArc_eq_zero_of_radius
      a ha x hx T hT
  have hmul : W * E + A * E = 0 := by
    calc
      W * E + A * E = (W + A) * E := by
        exact (add_mul W A E).symm
      _ = 0 * E := by
        exact congrArg (fun z : ℂ => z * E) hadd
      _ = 0 := by
        exact zero_mul E
  have hsub : W * E = -(A * E) := by
    calc
      W * E = (W * E + A * E) - A * E := by
        exact (add_sub_cancel_right (W * E) (A * E)).symm
      _ = 0 - A * E := by
        exact congrArg (fun z : ℂ => z - A * E) hmul
      _ = -(A * E) := by
        exact zero_sub (A * E)
  have hwindow :
      W * E =
        ∫ t in Set.Icc (-T) T,
          (-1 / ((a : ℂ) + t * Complex.I)) *
            Complex.exp
              (Complex.I * (t : ℂ) * (x : ℂ)) *
            Complex.exp ((a : ℂ) * (x : ℂ)) :=
    scalarFourierLaplacePlemelj_positive_window_mul_exp_eq_window_with_exp
      a x T
  exact hwindow.symm.trans hsub

/-- Radius-qualified negative finite-window norm estimate from the compensated
lower-arc norm. -/
theorem scalarFourierLaplacePlemelj_negative_window_with_exp_norm_le_lowerArc_of_radius
    (a : ℝ) (ha : 0 < a) (x : ℝ) (hx : x < 0)
    (T : ℝ) (hT : 0 < T) :
      ‖(∫ t in Set.Icc (-T) T,
        (-1 / ((a : ℂ) + t * Complex.I)) *
          Complex.exp
            (Complex.I * (t : ℂ) * (x : ℂ)) *
          Complex.exp ((a : ℂ) * (x : ℂ)))‖
      ≤ ‖scalarFourierLaplacePlemelj_negativeLowerArc a x T *
          Complex.exp ((a : ℂ) * (x : ℂ))‖ := by
  let A : ℂ := scalarFourierLaplacePlemelj_negativeLowerArc a x T
  let E : ℂ := Complex.exp ((a : ℂ) * (x : ℂ))
  let Wexp : ℂ :=
    ∫ t in Set.Icc (-T) T,
      (-1 / ((a : ℂ) + t * Complex.I)) *
        Complex.exp
          (Complex.I * (t : ℂ) * (x : ℂ)) *
        Complex.exp ((a : ℂ) * (x : ℂ))
  have heq :
      Wexp = -(A * E) :=
    scalarFourierLaplacePlemelj_negative_window_with_exp_eq_neg_lowerArc_mul_exp_of_radius
      a ha x hx T hT
  calc
    ‖Wexp‖ = ‖-(A * E)‖ := by
      exact congrArg norm heq
    _ = ‖A * E‖ := by
      exact norm_neg (A * E)

/-- Negative-time away-from-zero compact-interval estimate for the normalized
scalar Fourier-Laplace Plemelj kernel. -/
theorem scalarFourierLaplacePlemelj_compactInterval_negative_awayZero_norm_bound_eventually
    (a : ℝ) (ha : 0 < a) (R δ : ℝ) (hδ : 0 < δ) :
    ∃ C : ℝ,
      0 ≤ C ∧
        ∀ᶠ T in atTop,
          ∀ x : ℝ,
            x ≤ -δ →
            ‖x‖ ≤ R →
              ‖(∫ t in Set.Icc (-T) T,
                (-1 / ((a : ℂ) + t * Complex.I)) *
                  Complex.exp
                    (Complex.I * (t : ℂ) * (x : ℂ)) *
                  Complex.exp ((a : ℂ) * (x : ℂ)))‖
              ≤ C := by
  match
    scalarFourierLaplacePlemelj_negativeLowerArc_awayZero_mulExp_norm_bound_eventually
      a ha R δ hδ
  with
  | ⟨Carc, hCarc_nonneg, harc⟩ =>
      exact
        ⟨Carc, hCarc_nonneg,
          (harc.and (eventually_gt_atTop (0 : ℝ))).mono
            (fun T hTpair x hxδ hxR =>
              have hxneg : x < 0 := by
                have hnegδ_neg : -δ < 0 := neg_lt_zero.mpr hδ
                exact hxδ.trans_lt hnegδ_neg
              have hwindow :
                  ‖(∫ t in Set.Icc (-T) T,
                    (-1 / ((a : ℂ) + t * Complex.I)) *
                      Complex.exp
                        (Complex.I * (t : ℂ) * (x : ℂ)) *
                      Complex.exp ((a : ℂ) * (x : ℂ)))‖
                  ≤ ‖scalarFourierLaplacePlemelj_negativeLowerArc a x T *
                      Complex.exp ((a : ℂ) * (x : ℂ))‖ :=
                scalarFourierLaplacePlemelj_negative_window_with_exp_norm_le_lowerArc_of_radius
                  a ha x hxneg T hTpair.2
              hwindow.trans (hTpair.1 x hxδ hxR)⟩

/-- Negative-time near-zero compact-interval estimate for the normalized
scalar Fourier-Laplace Plemelj kernel. -/
theorem scalarFourierLaplacePlemelj_compactInterval_negative_nearZero_norm_bound_eventually
    (a : ℝ) (ha : 0 < a) (R δ : ℝ) (hδ : 0 < δ) :
    ∃ C : ℝ,
      0 ≤ C ∧
        ∀ᶠ T in atTop,
          ∀ x : ℝ,
            x < 0 →
            -δ < x →
            ‖x‖ ≤ R →
              ‖(∫ t in Set.Icc (-T) T,
                (-1 / ((a : ℂ) + t * Complex.I)) *
                  Complex.exp
                    (Complex.I * (t : ℂ) * (x : ℂ)) *
                  Complex.exp ((a : ℂ) * (x : ℂ)))‖
              ≤ C := by
  match
    scalarFourierLaplacePlemelj_compactInterval_punctured_nearZero_norm_bound_eventually
      a ha R δ hδ
  with
  | ⟨C, hC_nonneg, hnear⟩ =>
      exact
        ⟨C, hC_nonneg,
          hnear.mono
            (fun T hT x hxneg hδx hxR =>
              have hx_ne : x ≠ 0 := ne_of_lt hxneg
              have h_abs_lt : ‖x‖ < δ := by
                calc
                  ‖x‖ = -x := by
                    exact (Real.norm_eq_abs x).trans (abs_of_neg hxneg)
                  _ < δ := by
                    exact neg_lt.mp hδx
              hT x hx_ne h_abs_lt hxR)⟩

/-- Assembly of the negative compact-interval estimate from its near-zero and
away-from-zero pieces. -/
theorem scalarFourierLaplacePlemelj_compactInterval_negative_norm_bound_eventually_of_split
    (a : ℝ) (ha : 0 < a) (R δ Cnear Caway : ℝ) (hδ : 0 < δ)
    (hCnear_nonneg : 0 ≤ Cnear) (hCaway_nonneg : 0 ≤ Caway)
    (hnear :
      ∀ᶠ T in atTop,
        ∀ x : ℝ,
          x < 0 →
          -δ < x →
          ‖x‖ ≤ R →
            ‖(∫ t in Set.Icc (-T) T,
              (-1 / ((a : ℂ) + t * Complex.I)) *
                Complex.exp
                  (Complex.I * (t : ℂ) * (x : ℂ)) *
                Complex.exp ((a : ℂ) * (x : ℂ)))‖
            ≤ Cnear)
    (haway :
      ∀ᶠ T in atTop,
        ∀ x : ℝ,
          x ≤ -δ →
          ‖x‖ ≤ R →
            ‖(∫ t in Set.Icc (-T) T,
              (-1 / ((a : ℂ) + t * Complex.I)) *
                Complex.exp
                  (Complex.I * (t : ℂ) * (x : ℂ)) *
                Complex.exp ((a : ℂ) * (x : ℂ)))‖
            ≤ Caway) :
    ∃ C : ℝ,
      0 ≤ C ∧
        ∀ᶠ T in atTop,
          ∀ x : ℝ,
            x < 0 →
            ‖x‖ ≤ R →
              ‖(∫ t in Set.Icc (-T) T,
                (-1 / ((a : ℂ) + t * Complex.I)) *
                  Complex.exp
                    (Complex.I * (t : ℂ) * (x : ℂ)) *
                  Complex.exp ((a : ℂ) * (x : ℂ)))‖
              ≤ C := by
  let C : ℝ := max Cnear Caway
  have hC_nonneg : 0 ≤ C := by
    unfold C
    exact hCnear_nonneg.trans (le_max_left Cnear Caway)
  have hnear_le : Cnear ≤ C := by
    unfold C
    exact le_max_left Cnear Caway
  have haway_le : Caway ≤ C := by
    unfold C
    exact le_max_right Cnear Caway
  exact
    ⟨C, hC_nonneg,
      hnear.and haway |>.mono
        (fun T hsplit =>
          fun x hxneg hxR =>
            match lt_or_ge (-δ) x with
            | Or.inl hx_near =>
                (hsplit.1 x hxneg hx_near hxR).trans hnear_le
            | Or.inr hx_not_near =>
                (hsplit.2 x hx_not_near hxR).trans haway_le)⟩

/-- Negative-time compact-interval estimate for the normalized scalar
Fourier-Laplace Plemelj kernel. -/
theorem scalarFourierLaplacePlemelj_compactInterval_negative_norm_bound_eventually
    (a : ℝ) (ha : 0 < a) (R : ℝ) :
    ∃ C : ℝ,
      0 ≤ C ∧
        ∀ᶠ T in atTop,
          ∀ x : ℝ,
            x < 0 →
            ‖x‖ ≤ R →
              ‖(∫ t in Set.Icc (-T) T,
                (-1 / ((a : ℂ) + t * Complex.I)) *
                  Complex.exp
                    (Complex.I * (t : ℂ) * (x : ℂ)) *
                  Complex.exp ((a : ℂ) * (x : ℂ)))‖
              ≤ C := by
  let δ : ℝ := 1
  have hδ : 0 < δ := by
    unfold δ
    exact zero_lt_one
  match scalarFourierLaplacePlemelj_compactInterval_negative_nearZero_norm_bound_eventually
    a ha R δ hδ with
  | ⟨Cnear, hCnear_nonneg, hnear⟩ =>
      match scalarFourierLaplacePlemelj_compactInterval_negative_awayZero_norm_bound_eventually
        a ha R δ hδ with
      | ⟨Caway, hCaway_nonneg, haway⟩ =>
          exact
            scalarFourierLaplacePlemelj_compactInterval_negative_norm_bound_eventually_of_split
              a ha R δ Cnear Caway hδ hCnear_nonneg hCaway_nonneg
              hnear haway

/-- Zero-time compact-interval estimate for the normalized scalar
Fourier-Laplace Plemelj kernel. -/
theorem scalarFourierLaplacePlemelj_compactInterval_zero_norm_bound
    (a : ℝ) (ha : 0 < a) (R T x : ℝ) (hx_zero : x = 0) :
    ‖(∫ t in Set.Icc (-T) T,
      (-1 / ((a : ℂ) + t * Complex.I)) *
        Complex.exp
          (Complex.I * (t : ℂ) * (x : ℂ)) *
        Complex.exp ((a : ℂ) * (x : ℂ)))‖
      ≤ 2 * (Real.pi + 1) := by
  exact
    scalarFourierLaplacePlemelj_unweighted_window_mul_exp_uniform_bound_zero
      a ha T x hx_zero

/-- The maximum of the two one-sided compact-interval constants and the
zero-time constant is a common compact-interval Plemelj constant. -/
theorem scalarFourierLaplacePlemelj_compactInterval_commonConstant_bound
    (a : ℝ) (ha : 0 < a) (R Cpos Cneg : ℝ)
    (hCpos_nonneg : 0 ≤ Cpos) (hCneg_nonneg : 0 ≤ Cneg)
    (hpos :
      ∀ᶠ T in atTop,
        ∀ x : ℝ,
          0 < x →
          ‖x‖ ≤ R →
            ‖(∫ t in Set.Icc (-T) T,
              (-1 / ((a : ℂ) + t * Complex.I)) *
                Complex.exp
                  (Complex.I * (t : ℂ) * (x : ℂ)) *
                Complex.exp ((a : ℂ) * (x : ℂ)))‖
            ≤ Cpos)
    (hneg :
      ∀ᶠ T in atTop,
        ∀ x : ℝ,
          x < 0 →
          ‖x‖ ≤ R →
            ‖(∫ t in Set.Icc (-T) T,
              (-1 / ((a : ℂ) + t * Complex.I)) *
                Complex.exp
                  (Complex.I * (t : ℂ) * (x : ℂ)) *
                Complex.exp ((a : ℂ) * (x : ℂ)))‖
            ≤ Cneg) :
    ∃ C : ℝ,
      0 ≤ C ∧
        ∀ᶠ T in atTop,
          ∀ x : ℝ,
            ‖x‖ ≤ R →
              ‖(∫ t in Set.Icc (-T) T,
                (-1 / ((a : ℂ) + t * Complex.I)) *
                  Complex.exp
                    (Complex.I * (t : ℂ) * (x : ℂ)) *
                  Complex.exp ((a : ℂ) * (x : ℂ)))‖
              ≤ C := by
  let Czero : ℝ := 2 * (Real.pi + 1)
  let C : ℝ := max (max Cpos Cneg) Czero
  have hCzero_nonneg : 0 ≤ Czero := by
    unfold Czero
    exact mul_nonneg zero_le_two
      (add_nonneg Real.pi_nonneg zero_le_one)
  have hC_nonneg : 0 ≤ C := by
    unfold C
    exact le_max_of_le_right hCzero_nonneg
  have hCpos_le : Cpos ≤ C := by
    unfold C
    exact (le_max_left Cpos Cneg).trans (le_max_left (max Cpos Cneg) Czero)
  have hCneg_le : Cneg ≤ C := by
    unfold C
    exact (le_max_right Cpos Cneg).trans (le_max_left (max Cpos Cneg) Czero)
  have hCzero_le : Czero ≤ C := by
    unfold C
    exact le_max_right (max Cpos Cneg) Czero
  exact
    ⟨C, hC_nonneg,
      hpos.and hneg |>.mono
        (fun T hboth =>
          fun x hxR =>
            match lt_trichotomy x 0 with
            | Or.inl hxneg =>
                (hboth.2 x hxneg hxR).trans hCneg_le
            | Or.inr hnonneg =>
                match hnonneg with
                | Or.inl hxzero =>
                    (scalarFourierLaplacePlemelj_compactInterval_zero_norm_bound
                      a ha R T x hxzero).trans hCzero_le
                | Or.inr hxpos =>
                    (hboth.1 x hxpos hxR).trans hCpos_le)⟩

/-- Compact-interval estimate for the normalized scalar Fourier-Laplace
Plemelj kernel. -/
theorem scalarFourierLaplacePlemelj_compactInterval_norm_bound_eventually
    (a : ℝ) (ha : 0 < a) (R : ℝ) :
    ∃ C : ℝ,
      0 ≤ C ∧
        ∀ᶠ T in atTop,
          ∀ x : ℝ,
            ‖x‖ ≤ R →
              ‖(∫ t in Set.Icc (-T) T,
                (-1 / ((a : ℂ) + t * Complex.I)) *
                  Complex.exp
                    (Complex.I * (t : ℂ) * (x : ℂ)) *
                  Complex.exp ((a : ℂ) * (x : ℂ)))‖
              ≤ C := by
  match scalarFourierLaplacePlemelj_compactInterval_positive_norm_bound_eventually
    a ha R with
  | ⟨Cpos, hCpos_nonneg, hpos⟩ =>
      match scalarFourierLaplacePlemelj_compactInterval_negative_norm_bound_eventually
        a ha R with
      | ⟨Cneg, hCneg_nonneg, hneg⟩ =>
          exact
            scalarFourierLaplacePlemelj_compactInterval_commonConstant_bound
              a ha R Cpos Cneg hCpos_nonneg hCneg_nonneg hpos hneg

/-- Compact-interval scalar-window estimate for the fixed-right-line Cauchy
kernel.

This is the analytic core of compact-support domination: on every bounded
time interval, the finite scalar Cauchy windows are eventually uniformly
bounded in the truncation radius. -/
theorem fixedRightLine_scalarCauchyWindow_compactInterval_norm_bound_eventually
    (R c : ℝ) (hc : 1 < c) :
    ∃ C : ℝ,
      0 ≤ C ∧
        ∀ᶠ T in atTop,
          ∀ x : ℝ,
            ‖x‖ ≤ R →
              ‖(∫ t in Set.Icc (-T) T,
                (-1 / (((c : ℂ) + t * Complex.I) - 1)) *
                  Complex.exp
                    (Complex.I * (t : ℂ) * (x : ℂ)) *
                  Complex.exp (((c - 1 : ℝ) : ℂ) * (x : ℂ)))‖
              ≤ C := by
  have ha : 0 < c - 1 :=
    sub_pos.mpr hc
  match scalarFourierLaplacePlemelj_compactInterval_norm_bound_eventually
    (c - 1) ha R with
  | ⟨C, hC_nonneg, hC_eventual⟩ =>
      exact
        ⟨C, hC_nonneg,
          hC_eventual.mono
            (fun T hT =>
              fun x hx =>
                Eq.subst
                  (motive := fun z : ℂ => ‖z‖ ≤ C)
                  (fixedRightLine_scalarCauchyWindow_eq_normalizedLaplaceWindow
                    c x T).symm
                  (hT x hx))⟩

/-- Compact-support scalar-window estimate on the time support of the kernel.

This is the local finite-window bound owned by the compact-support Cauchy
projection layer.  The scalar Cauchy windows are only required uniformly on
the compact set where the time kernel can be nonzero. -/
theorem fixedRightLine_scalarCauchyWindow_tsupport_norm_bound_eventually
    (K : ℝ → ℂ) (hK_cont : Continuous K) (hK_compact : HasCompactSupport K)
    (hK_smooth : ContDiff ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) K)
    (c : ℝ) (hc : 1 < c) :
    ∃ C : ℝ,
      0 ≤ C ∧
        ∀ᶠ T in atTop,
          ∀ x : ℝ,
            x ∈ tsupport K →
              ‖(∫ t in Set.Icc (-T) T,
                (-1 / (((c : ℂ) + t * Complex.I) - 1)) *
                  Complex.exp
                    (Complex.I * (t : ℂ) * (x : ℂ)) *
                  Complex.exp (((c - 1 : ℝ) : ℂ) * (x : ℂ)))‖
              ≤ C := by
  have hbounded : Bornology.IsBounded (tsupport K) :=
    hK_compact.isBounded
  match hbounded.exists_norm_le with
  | ⟨R, hR⟩ =>
      match fixedRightLine_scalarCauchyWindow_compactInterval_norm_bound_eventually
        R c hc with
      | ⟨C, hC_nonneg, hC_eventual⟩ =>
          exact
            ⟨C, hC_nonneg,
              hC_eventual.mono
                (fun T hT =>
                  fun x hx =>
                    hT x (hR x hx))⟩

/-- Compact-support paired-window estimate for the fixed-right-line scalar
Cauchy kernel.

This is the true domination source: after pairing with the compactly supported
kernel, the finite scalar Cauchy windows are bounded by a constant times
`‖K x‖` eventually in the truncation radius. -/
theorem fixedRightLine_scalarCauchyWindow_compactSupport_paired_norm_bound_eventually
    (K : ℝ → ℂ) (hK_cont : Continuous K) (hK_compact : HasCompactSupport K)
    (hK_smooth : ContDiff ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) K)
    (c : ℝ) (hc : 1 < c) :
    ∃ C : ℝ,
      0 ≤ C ∧
        ∀ᶠ T in atTop,
          ∀ᵐ x ∂volume,
            ‖K x *
              (∫ t in Set.Icc (-T) T,
                (-1 / (((c : ℂ) + t * Complex.I) - 1)) *
                  Complex.exp
                    (Complex.I * (t : ℂ) * (x : ℂ)) *
                  Complex.exp (((c - 1 : ℝ) : ℂ) * (x : ℂ)))‖
              ≤ C * ‖K x‖ := by
  match
    fixedRightLine_scalarCauchyWindow_tsupport_norm_bound_eventually
      K hK_cont hK_compact hK_smooth c hc
  with
  | ⟨C, hC_nonneg, hC_eventual⟩ =>
      exact
        ⟨C, hC_nonneg,
          hC_eventual.mono
            (fun T hT =>
              Eventually.of_forall
                (fun x : ℝ =>
                  if hx_support : x ∈ tsupport K then
                    let W : ℂ :=
                      ∫ t in Set.Icc (-T) T,
                        (-1 / (((c : ℂ) + t * Complex.I) - 1)) *
                          Complex.exp
                            (Complex.I * (t : ℂ) * (x : ℂ)) *
                          Complex.exp (((c - 1 : ℝ) : ℂ) * (x : ℂ))
                    have hW : ‖W‖ ≤ C :=
                      hT x hx_support
                    have hmul : ‖K x‖ * ‖W‖ ≤ ‖K x‖ * C :=
                      mul_le_mul_of_nonneg_left hW (norm_nonneg (K x))
                    calc
                      ‖K x * W‖ = ‖K x‖ * ‖W‖ := by
                        exact norm_mul (K x) W
                      _ ≤ ‖K x‖ * C := hmul
                      _ = C * ‖K x‖ := by
                        exact mul_comm ‖K x‖ C
                  else
                    let W : ℂ :=
                      ∫ t in Set.Icc (-T) T,
                        (-1 / (((c : ℂ) + t * Complex.I) - 1)) *
                          Complex.exp
                            (Complex.I * (t : ℂ) * (x : ℂ)) *
                          Complex.exp (((c - 1 : ℝ) : ℂ) * (x : ℂ))
                    have hK_zero : K x = 0 :=
                      image_eq_zero_of_nmem_tsupport hx_support
                    have hleft : ‖K x * W‖ = 0 := by
                      calc
                        ‖K x * W‖ = ‖(0 : ℂ) * W‖ := by
                          exact congrArg (fun z : ℂ => ‖z * W‖) hK_zero
                        _ = ‖(0 : ℂ)‖ := by
                          exact congrArg norm (zero_mul W)
                        _ = 0 := norm_zero
                    have hright : C * ‖K x‖ = 0 := by
                      calc
                        C * ‖K x‖ = C * ‖(0 : ℂ)‖ := by
                          exact congrArg (fun z : ℂ => C * ‖z‖) hK_zero
                        _ = C * 0 := by
                          exact congrArg (fun r : ℝ => C * r) norm_zero
                        _ = 0 := by
                          exact mul_zero C
                    Eq.subst
                      (motive := fun y : ℝ => ‖K x * W‖ ≤ y)
                      hright.symm
                      (Eq.subst
                        (motive := fun y : ℝ => y ≤ 0)
                        hleft.symm
                        (le_refl 0))))⟩

/-- Uniform compact-support domination for the paired scalar Cauchy windows. -/
theorem fixedRightLine_scalarCauchyWindow_compactSupport_dominated
    (K : ℝ → ℂ) (hK_cont : Continuous K) (hK_compact : HasCompactSupport K)
    (hK_smooth : ContDiff ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) K)
    (c : ℝ) (hc : 1 < c) :
    ∃ G : ℝ → ℝ,
      Integrable G ∧
        0 ≤ᵐ[volume] G ∧
          ∀ᶠ T in atTop,
            ∀ᵐ x ∂volume,
              ‖K x *
                (∫ t in Set.Icc (-T) T,
                  (-1 / (((c : ℂ) + t * Complex.I) - 1)) *
                    Complex.exp
                      (Complex.I * (t : ℂ) * (x : ℂ)) *
                    Complex.exp (((c - 1 : ℝ) : ℂ) * (x : ℂ)))‖
                ≤ G x := by
  match
    fixedRightLine_scalarCauchyWindow_compactSupport_paired_norm_bound_eventually
      K hK_cont hK_compact hK_smooth c hc
  with
  | ⟨C, hC_nonneg, hC_eventual⟩ =>
      let G : ℝ → ℝ := fun x : ℝ => C * ‖K x‖
      have hK_integrable : Integrable K volume :=
        hK_cont.integrable_of_hasCompactSupport hK_compact
      have hG_integrable : Integrable G volume :=
        hK_integrable.norm.const_mul C
      have hG_nonnegative : 0 ≤ᵐ[volume] G :=
        Eventually.of_forall
          (fun x : ℝ =>
            mul_nonneg hC_nonneg (norm_nonneg (K x)))
      exact
        ⟨G, hG_integrable, hG_nonnegative,
          hC_eventual.mono
            (fun T hT =>
              hT.mono
                (fun _ hx => hx))⟩

/-- Joint continuity of the finite scalar fixed-right-line Cauchy-window
integrand in the space and frequency variables. -/
theorem fixedRightLine_scalarCauchyWindow_integrand_joint_continuous
    (c : ℝ) (hc : 1 < c) :
    Continuous
      (fun p : ℝ × ℝ =>
        (-1 / (((c : ℂ) + p.2 * Complex.I) - 1)) *
          Complex.exp
            (Complex.I * (p.2 : ℂ) * (p.1 : ℂ)) *
          Complex.exp (((c - 1 : ℝ) : ℂ) * (p.1 : ℂ))) := by
  have hden :
      Continuous
        (fun p : ℝ × ℝ =>
          (((c : ℂ) + p.2 * Complex.I) - 1)) :=
    (continuous_const.add
      ((Complex.continuous_ofReal.comp continuous_snd).mul continuous_const)).sub
      continuous_const
  have hden_ne :
      ∀ p : ℝ × ℝ,
        (((c : ℂ) + p.2 * Complex.I) - 1) ≠ 0 :=
    fun p : ℝ × ℝ =>
      fixedRightLine_cauchyDenominator_ne_zero c p.2 hc
  have hscalar :
      Continuous
        (fun p : ℝ × ℝ =>
          -1 / (((c : ℂ) + p.2 * Complex.I) - 1)) :=
    continuous_const.div hden hden_ne
  have hphase :
      Continuous
        (fun p : ℝ × ℝ =>
          Complex.I * (p.2 : ℂ) * (p.1 : ℂ)) :=
    (continuous_const.mul
      (Complex.continuous_ofReal.comp continuous_snd)).mul
        (Complex.continuous_ofReal.comp continuous_fst)
  have hweight :
      Continuous
        (fun p : ℝ × ℝ =>
          ((c - 1 : ℝ) : ℂ) * (p.1 : ℂ)) :=
    continuous_const.mul
      (Complex.continuous_ofReal.comp continuous_fst)
  exact
    (hscalar.mul (Complex.continuous_exp.comp hphase)).mul
      (Complex.continuous_exp.comp hweight)

/-- Continuity of each finite scalar Cauchy window before pairing with the
compact-support kernel. -/
theorem fixedRightLine_scalarCauchyWindow_continuous
    (c : ℝ) (hc : 1 < c) (T : ℝ) :
    Continuous
      (fun x : ℝ =>
        ∫ t in Set.Icc (-T) T,
          (-1 / (((c : ℂ) + t * Complex.I) - 1)) *
            Complex.exp
              (Complex.I * (t : ℂ) * (x : ℂ)) *
            Complex.exp (((c - 1 : ℝ) : ℂ) * (x : ℂ))) :=
  continuous_parametric_integral_of_continuous
    (fixedRightLine_scalarCauchyWindow_integrand_joint_continuous c hc)
    isCompact_Icc

/-- Continuity in the time variable of each finite scalar Cauchy window paired
against the smooth compact-support kernel. -/
theorem fixedRightLine_scalarCauchyWindow_paired_continuous
    (K : ℝ → ℂ) (hK_cont : Continuous K) (hK_compact : HasCompactSupport K)
    (hK_smooth : ContDiff ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) K)
    (c : ℝ) (hc : 1 < c) (T : ℝ) :
    Continuous
      (fun x : ℝ =>
        K x *
          (∫ t in Set.Icc (-T) T,
            (-1 / (((c : ℂ) + t * Complex.I) - 1)) *
              Complex.exp
                (Complex.I * (t : ℂ) * (x : ℂ)) *
              Complex.exp (((c - 1 : ℝ) : ℂ) * (x : ℂ)))) := by
  exact hK_cont.mul
    (fixedRightLine_scalarCauchyWindow_continuous c hc T)

/-- A.e.-strong measurability of the paired scalar Cauchy window kernels. -/
theorem fixedRightLine_scalarCauchyWindow_paired_aestronglyMeasurable_eventually
    (K : ℝ → ℂ) (hK_cont : Continuous K) (hK_compact : HasCompactSupport K)
    (hK_smooth : ContDiff ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) K)
    (c : ℝ) (hc : 1 < c) :
    ∀ᶠ T in atTop,
      AEStronglyMeasurable
        (fun x : ℝ =>
          K x *
            (∫ t in Set.Icc (-T) T,
              (-1 / (((c : ℂ) + t * Complex.I) - 1)) *
                Complex.exp
                  (Complex.I * (t : ℂ) * (x : ℂ)) *
                Complex.exp (((c - 1 : ℝ) : ℂ) * (x : ℂ))))
        volume := by
  exact
    Eventually.of_forall
      (fun T : ℝ =>
        (fixedRightLine_scalarCauchyWindow_paired_continuous
          K hK_cont hK_compact hK_smooth c hc T).aestronglyMeasurable)

/-- Positive-time paired scalar Cauchy window limit after multiplication by
the compact-support kernel. -/
theorem fixedRightLine_scalarCauchyWindow_paired_pointwise_tendsto_positive
    (K : ℝ → ℂ) (c : ℝ) (hc : 1 < c) (x : ℝ) (hx : 0 < x) :
    Tendsto
      (fun T : ℝ =>
        K x *
          (∫ t in Set.Icc (-T) T,
            (-1 / (((c : ℂ) + t * Complex.I) - 1)) *
              Complex.exp
                (Complex.I * (t : ℂ) * (x : ℂ)) *
              Complex.exp (((c - 1 : ℝ) : ℂ) * (x : ℂ))))
      atTop
      (𝓝
        (Set.indicator (Set.Ioi (0 : ℝ))
          (fun y : ℝ => (-2 * (Real.pi : ℂ)) * K y) x)) := by
  have hscalar :
      Tendsto
        (fun T : ℝ =>
          ∫ t in Set.Icc (-T) T,
            (-1 / (((c : ℂ) + t * Complex.I) - 1)) *
              Complex.exp
                (Complex.I * (t : ℂ) * (x : ℂ)) *
              Complex.exp (((c - 1 : ℝ) : ℂ) * (x : ℂ)))
        atTop
        (𝓝 (-2 * (Real.pi : ℂ))) :=
    fixedRightLine_scalarCauchyWindow_pointwise_tendsto_positive
      c hc x hx
  have hmul :
      Tendsto
        (fun T : ℝ =>
          K x *
            (∫ t in Set.Icc (-T) T,
              (-1 / (((c : ℂ) + t * Complex.I) - 1)) *
                Complex.exp
                  (Complex.I * (t : ℂ) * (x : ℂ)) *
                Complex.exp (((c - 1 : ℝ) : ℂ) * (x : ℂ))))
        atTop
        (𝓝 (K x * (-2 * (Real.pi : ℂ)))) :=
    tendsto_const_nhds.mul hscalar
  have hcomm :
      K x * (-2 * (Real.pi : ℂ)) =
        (-2 * (Real.pi : ℂ)) * K x :=
    mul_comm (K x) (-2 * (Real.pi : ℂ))
  have hindicator :
      Set.indicator (Set.Ioi (0 : ℝ))
          (fun y : ℝ => (-2 * (Real.pi : ℂ)) * K y) x =
        (-2 * (Real.pi : ℂ)) * K x :=
    indicator_of_mem hx
      (fun y : ℝ => (-2 * (Real.pi : ℂ)) * K y)
  have htarget :
      K x * (-2 * (Real.pi : ℂ)) =
        Set.indicator (Set.Ioi (0 : ℝ))
          (fun y : ℝ => (-2 * (Real.pi : ℂ)) * K y) x :=
    hcomm.trans hindicator.symm
  exact htarget ▸ hmul

/-- Negative-time paired scalar Cauchy window limit after multiplication by
the compact-support kernel. -/
theorem fixedRightLine_scalarCauchyWindow_paired_pointwise_tendsto_negative
    (K : ℝ → ℂ) (c : ℝ) (hc : 1 < c) (x : ℝ) (hx : x < 0) :
    Tendsto
      (fun T : ℝ =>
        K x *
          (∫ t in Set.Icc (-T) T,
            (-1 / (((c : ℂ) + t * Complex.I) - 1)) *
              Complex.exp
                (Complex.I * (t : ℂ) * (x : ℂ)) *
              Complex.exp (((c - 1 : ℝ) : ℂ) * (x : ℂ))))
      atTop
      (𝓝
        (Set.indicator (Set.Ioi (0 : ℝ))
          (fun y : ℝ => (-2 * (Real.pi : ℂ)) * K y) x)) := by
  have hscalar :
      Tendsto
        (fun T : ℝ =>
          ∫ t in Set.Icc (-T) T,
            (-1 / (((c : ℂ) + t * Complex.I) - 1)) *
              Complex.exp
                (Complex.I * (t : ℂ) * (x : ℂ)) *
              Complex.exp (((c - 1 : ℝ) : ℂ) * (x : ℂ)))
        atTop
        (𝓝 0) :=
    fixedRightLine_scalarCauchyWindow_pointwise_tendsto_negative
      c hc x hx
  have hmul :
      Tendsto
        (fun T : ℝ =>
          K x *
            (∫ t in Set.Icc (-T) T,
              (-1 / (((c : ℂ) + t * Complex.I) - 1)) *
                Complex.exp
                  (Complex.I * (t : ℂ) * (x : ℂ)) *
                Complex.exp (((c - 1 : ℝ) : ℂ) * (x : ℂ))))
        atTop
        (𝓝 (K x * 0)) :=
    tendsto_const_nhds.mul hscalar
  have hzero :
      K x * (0 : ℂ) = 0 :=
    mul_zero (K x)
  have hnotMem :
      x ∉ Set.Ioi (0 : ℝ) :=
    fun hxpos => not_lt_of_gt hx hxpos
  have hindicator :
      Set.indicator (Set.Ioi (0 : ℝ))
          (fun y : ℝ => (-2 * (Real.pi : ℂ)) * K y) x =
        0 :=
    indicator_of_not_mem hnotMem
      (fun y : ℝ => (-2 * (Real.pi : ℂ)) * K y)
  have htarget :
      K x * (0 : ℂ) =
        Set.indicator (Set.Ioi (0 : ℝ))
          (fun y : ℝ => (-2 * (Real.pi : ℂ)) * K y) x :=
    hzero.trans hindicator.symm
  exact htarget ▸ hmul

/-- A.e. paired scalar Cauchy window limit against the open positive half-line. -/
theorem fixedRightLine_scalarCauchyWindow_ae_tendsto_openHalfLineKernel
    (K : ℝ → ℂ) (hK_cont : Continuous K) (hK_compact : HasCompactSupport K)
    (hK_smooth : ContDiff ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) K)
    (c : ℝ) (hc : 1 < c) :
    ∀ᵐ x ∂volume,
      Tendsto
        (fun T : ℝ =>
          K x *
            (∫ t in Set.Icc (-T) T,
              (-1 / (((c : ℂ) + t * Complex.I) - 1)) *
                Complex.exp
                  (Complex.I * (t : ℂ) * (x : ℂ)) *
                Complex.exp (((c - 1 : ℝ) : ℂ) * (x : ℂ))))
        atTop
        (𝓝
          (Set.indicator (Set.Ioi (0 : ℝ))
            (fun y : ℝ => (-2 * (Real.pi : ℂ)) * K y) x)) := by
  have hnotEndpoint :
      ∀ᵐ x ∂volume, x ∉ ({0} : Set ℝ) :=
    (Set.countable_singleton (0 : ℝ)).ae_not_mem volume
  exact
    hnotEndpoint.mono
      (fun x hxNotEndpoint =>
        match lt_or_gt_of_ne
          (fun hxEq : x = 0 =>
            hxNotEndpoint (Set.mem_singleton_iff.mpr hxEq)) with
        | Or.inl hxneg =>
            fixedRightLine_scalarCauchyWindow_paired_pointwise_tendsto_negative
              K c hc x hxneg
        | Or.inr hxpos =>
            fixedRightLine_scalarCauchyWindow_paired_pointwise_tendsto_positive
              K c hc x hxpos)

/-- Paired symmetric-window scalar Cauchy kernel convergence against a smooth
compact support kernel, with the open positive half-line as boundary value. -/
theorem fixedRightLine_scalarCauchyWindow_paired_tendsto_openHalfLineIntegral
    (K : ℝ → ℂ) (hK_cont : Continuous K) (hK_compact : HasCompactSupport K)
    (hK_smooth : ContDiff ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) K)
    (c : ℝ) (hc : 1 < c) :
    Tendsto
      (fun T : ℝ =>
        ∫ x : ℝ,
          K x *
            (∫ t in Set.Icc (-T) T,
              (-1 / (((c : ℂ) + t * Complex.I) - 1)) *
                Complex.exp
                  (Complex.I * (t : ℂ) * (x : ℂ)) *
                Complex.exp (((c - 1 : ℝ) : ℂ) * (x : ℂ))))
      atTop
      (𝓝
        (∫ x in Set.Ioi (0 : ℝ),
          (-2 * (Real.pi : ℂ)) * K x)) := by
  match
    fixedRightLine_scalarCauchyWindow_compactSupport_dominated
      K hK_cont hK_compact hK_smooth c hc
  with
  | ⟨G, hG_int, hG_nonneg, hG_bound⟩ =>
      have hmeas :
          ∀ᶠ T in atTop,
            AEStronglyMeasurable
              (fun x : ℝ =>
                K x *
                  (∫ t in Set.Icc (-T) T,
                    (-1 / (((c : ℂ) + t * Complex.I) - 1)) *
                      Complex.exp
                        (Complex.I * (t : ℂ) * (x : ℂ)) *
                      Complex.exp (((c - 1 : ℝ) : ℂ) * (x : ℂ))))
              volume :=
        fixedRightLine_scalarCauchyWindow_paired_aestronglyMeasurable_eventually
          K hK_cont hK_compact hK_smooth c hc
      have hae :
          ∀ᵐ x ∂volume,
            Tendsto
              (fun T : ℝ =>
                K x *
                  (∫ t in Set.Icc (-T) T,
                    (-1 / (((c : ℂ) + t * Complex.I) - 1)) *
                      Complex.exp
                        (Complex.I * (t : ℂ) * (x : ℂ)) *
                      Complex.exp (((c - 1 : ℝ) : ℂ) * (x : ℂ))))
              atTop
              (𝓝
                (Set.indicator (Set.Ioi (0 : ℝ))
                  (fun y : ℝ => (-2 * (Real.pi : ℂ)) * K y) x)) :=
        fixedRightLine_scalarCauchyWindow_ae_tendsto_openHalfLineKernel
          K hK_cont hK_compact hK_smooth c hc
      have htarget :
          (∫ x : ℝ,
            Set.indicator (Set.Ioi (0 : ℝ))
              (fun y : ℝ => (-2 * (Real.pi : ℂ)) * K y) x) =
            ∫ x in Set.Ioi (0 : ℝ),
              (-2 * (Real.pi : ℂ)) * K x := by
        exact integral_indicator measurableSet_Ioi
      exact
        htarget ▸
          tendsto_integral_filter_of_dominated_convergence
            G hmeas hG_bound hG_int hae

/-- Paired symmetric-window scalar Cauchy kernel convergence against a smooth
compact support kernel. -/
theorem fixedRightLine_scalarCauchyWindow_paired_tendsto_indicatorIntegral
    (K : ℝ → ℂ) (hK_cont : Continuous K) (hK_compact : HasCompactSupport K)
    (hK_smooth : ContDiff ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) K)
    (c : ℝ) (hc : 1 < c) :
    Tendsto
      (fun T : ℝ =>
        ∫ x : ℝ,
          K x *
            (∫ t in Set.Icc (-T) T,
              (-1 / (((c : ℂ) + t * Complex.I) - 1)) *
                Complex.exp
                  (Complex.I * (t : ℂ) * (x : ℂ)) *
                Complex.exp (((c - 1 : ℝ) : ℂ) * (x : ℂ))))
      atTop
      (𝓝
        (∫ x : ℝ,
          K x *
            Set.indicator (Set.Ici (0 : ℝ))
              (fun _ : ℝ => (-2 * (Real.pi : ℂ))) x)) := by
  have hopen :
      Tendsto
        (fun T : ℝ =>
          ∫ x : ℝ,
            K x *
              (∫ t in Set.Icc (-T) T,
                (-1 / (((c : ℂ) + t * Complex.I) - 1)) *
                  Complex.exp
                    (Complex.I * (t : ℂ) * (x : ℂ)) *
                  Complex.exp (((c - 1 : ℝ) : ℂ) * (x : ℂ))))
        atTop
        (𝓝
          (∫ x in Set.Ioi (0 : ℝ),
            (-2 * (Real.pi : ℂ)) * K x)) :=
    fixedRightLine_scalarCauchyWindow_paired_tendsto_openHalfLineIntegral
      K hK_cont hK_compact hK_smooth c hc
  have hclosed :
      (∫ x in Set.Ioi (0 : ℝ),
          (-2 * (Real.pi : ℂ)) * K x) =
        ∫ x in Set.Ici (0 : ℝ),
          (-2 * (Real.pi : ℂ)) * K x :=
    fixedRightLine_scalarProjection_Ioi_integral_eq_Ici_integral K
  have hindicator :
      (∫ x in Set.Ici (0 : ℝ),
          (-2 * (Real.pi : ℂ)) * K x) =
        (∫ x : ℝ,
          K x *
            Set.indicator (Set.Ici (0 : ℝ))
              (fun _ : ℝ => (-2 * (Real.pi : ℂ))) x) :=
    (fixedRightLine_fourierCauchy_scalarKernelIntegral_eq_oneSidedProjection
      K).symm
  exact hindicator ▸ hclosed ▸ hopen

/-- Paired symmetric-window Cauchy kernel convergence against a smooth compact
support kernel on the fixed right line. -/
theorem fixedRightLine_fourierCauchy_symmetricTruncation_tendsto_scalarKernelIntegral
    (K : ℝ → ℂ) (hK_cont : Continuous K) (hK_compact : HasCompactSupport K)
    (hK_smooth : ContDiff ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) K)
    (c : ℝ) (hc : 1 < c) :
    Tendsto
      (fun T : ℝ =>
        ∫ t in Set.Icc (-T) T,
          (-1 / (((c : ℂ) + t * Complex.I) - 1)) *
            (∫ x : ℝ,
              K x *
                Complex.exp
                  (Complex.I * (t : ℂ) * (x : ℂ)) *
                Complex.exp (((c - 1 : ℝ) : ℂ) * (x : ℂ))))
      atTop
      (𝓝
        (∫ x : ℝ,
          K x *
            Set.indicator (Set.Ici (0 : ℝ))
              (fun _ : ℝ => (-2 * (Real.pi : ℂ))) x)) := by
  have hscalar :
      Tendsto
        (fun T : ℝ =>
          ∫ x : ℝ,
            K x *
              (∫ t in Set.Icc (-T) T,
                (-1 / (((c : ℂ) + t * Complex.I) - 1)) *
                  Complex.exp
                    (Complex.I * (t : ℂ) * (x : ℂ)) *
                  Complex.exp (((c - 1 : ℝ) : ℂ) * (x : ℂ))))
        atTop
        (𝓝
          (∫ x : ℝ,
            K x *
              Set.indicator (Set.Ici (0 : ℝ))
                (fun _ : ℝ => (-2 * (Real.pi : ℂ))) x)) :=
    fixedRightLine_scalarCauchyWindow_paired_tendsto_indicatorIntegral
      K hK_cont hK_compact hK_smooth c hc
  have hfunctions :
      (fun T : ℝ =>
        ∫ t in Set.Icc (-T) T,
          (-1 / (((c : ℂ) + t * Complex.I) - 1)) *
            (∫ x : ℝ,
              K x *
                Complex.exp
                  (Complex.I * (t : ℂ) * (x : ℂ)) *
                Complex.exp (((c - 1 : ℝ) : ℂ) * (x : ℂ)))) =
      (fun T : ℝ =>
        ∫ x : ℝ,
          K x *
            (∫ t in Set.Icc (-T) T,
              (-1 / (((c : ℂ) + t * Complex.I) - 1)) *
                Complex.exp
                  (Complex.I * (t : ℂ) * (x : ℂ)) *
                Complex.exp (((c - 1 : ℝ) : ℂ) * (x : ℂ)))) :=
    funext
      (fun T : ℝ =>
        fixedRightLine_fourierCauchy_symmetricWindow_eq_scalarWindowIntegral
          K hK_cont hK_compact hK_smooth c hc T)
  exact hfunctions.symm ▸ hscalar

/-- Full-line Fourier-Cauchy inversion before collapsing the scalar Cauchy
kernel to the one-sided projection integral. -/
theorem fixedRightLine_fourierCauchy_fullLine_smooth_scalarKernelIntegral
    (K : ℝ → ℂ) (hK_cont : Continuous K) (hK_compact : HasCompactSupport K)
    (hK_smooth : ContDiff ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) K)
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
          Set.indicator (Set.Ici (0 : ℝ))
            (fun _ : ℝ => (-2 * (Real.pi : ℂ))) x := by
  have hfull :
      Tendsto
        (fun T : ℝ =>
          ∫ t in Set.Icc (-T) T,
            (-1 / (((c : ℂ) + t * Complex.I) - 1)) *
              (∫ x : ℝ,
                K x *
                  Complex.exp
                    (Complex.I * (t : ℂ) * (x : ℂ)) *
                  Complex.exp (((c - 1 : ℝ) : ℂ) * (x : ℂ))))
        atTop
        (𝓝
          (∫ t : ℝ,
            (-1 / (((c : ℂ) + t * Complex.I) - 1)) *
              (∫ x : ℝ,
                K x *
                  Complex.exp
                    (Complex.I * (t : ℂ) * (x : ℂ)) *
                  Complex.exp (((c - 1 : ℝ) : ℂ) * (x : ℂ))))) :=
    fixedRightLine_fourierCauchy_symmetricTruncation_tendsto_fullLine
      K hK_cont hK_compact hK_smooth c hc
  have hscalar :
      Tendsto
        (fun T : ℝ =>
          ∫ t in Set.Icc (-T) T,
            (-1 / (((c : ℂ) + t * Complex.I) - 1)) *
              (∫ x : ℝ,
                K x *
                  Complex.exp
                    (Complex.I * (t : ℂ) * (x : ℂ)) *
                  Complex.exp (((c - 1 : ℝ) : ℂ) * (x : ℂ))))
        atTop
        (𝓝
          (∫ x : ℝ,
            K x *
              Set.indicator (Set.Ici (0 : ℝ))
                (fun _ : ℝ => (-2 * (Real.pi : ℂ))) x)) :=
    fixedRightLine_fourierCauchy_symmetricTruncation_tendsto_scalarKernelIntegral
      K hK_cont hK_compact hK_smooth c hc
  exact tendsto_nhds_unique hfull hscalar

/-- Smooth product-level Cauchy projection on the fixed right line.

This is the ordinary-integral owner statement: smooth compact support supplies
the decay needed to interpret the Cauchy multiplier as a genuine full-line
integral before taking the one-sided boundary projection. -/
theorem fixedRightLine_fourierCauchy_fullLine_smooth_oneSidedProjection
    (K : ℝ → ℂ) (hK_cont : Continuous K) (hK_compact : HasCompactSupport K)
    (hK_smooth : ContDiff ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) K)
    (c : ℝ) (hc : 1 < c) :
    (∫ t : ℝ,
        (-1 / (((c : ℂ) + t * Complex.I) - 1)) *
          (∫ x : ℝ,
            K x *
              Complex.exp
                (Complex.I * (t : ℂ) * (x : ℂ)) *
              Complex.exp (((c - 1 : ℝ) : ℂ) * (x : ℂ)))) =
      ∫ x in Set.Ici (0 : ℝ),
        (-2 * (Real.pi : ℂ)) * K x := by
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
            Set.indicator (Set.Ici (0 : ℝ))
              (fun _ : ℝ => (-2 * (Real.pi : ℂ))) x := by
          exact
            fixedRightLine_fourierCauchy_fullLine_smooth_scalarKernelIntegral
              K hK_cont hK_compact hK_smooth c hc
    _ =
        ∫ x in Set.Ici (0 : ℝ),
          (-2 * (Real.pi : ℂ)) * K x := by
          exact
            fixedRightLine_fourierCauchy_scalarKernelIntegral_eq_oneSidedProjection
              K

/-- Symmetric truncations of the smooth fixed-line Fourier-Cauchy multiplier
converge to the positive-time one-sided projection. -/
theorem fixedRightLine_fourierCauchy_symmetricTruncation_tendsto_oneSidedProjection
    (K : ℝ → ℂ) (hK_cont : Continuous K) (hK_compact : HasCompactSupport K)
    (hK_smooth : ContDiff ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) K)
    (c : ℝ) (hc : 1 < c) :
    Tendsto
      (fun T : ℝ =>
        ∫ t in Set.Icc (-T) T,
          (-1 / (((c : ℂ) + t * Complex.I) - 1)) *
            (∫ x : ℝ,
              K x *
                Complex.exp
                  (Complex.I * (t : ℂ) * (x : ℂ)) *
                Complex.exp (((c - 1 : ℝ) : ℂ) * (x : ℂ))))
      atTop
      (𝓝
        (∫ x in Set.Ici (0 : ℝ),
          (-2 * (Real.pi : ℂ)) * K x)) := by
  have hfull :
      Tendsto
        (fun T : ℝ =>
          ∫ t in Set.Icc (-T) T,
            (-1 / (((c : ℂ) + t * Complex.I) - 1)) *
              (∫ x : ℝ,
                K x *
                  Complex.exp
                    (Complex.I * (t : ℂ) * (x : ℂ)) *
                  Complex.exp (((c - 1 : ℝ) : ℂ) * (x : ℂ))))
        atTop
        (𝓝
          (∫ t : ℝ,
            (-1 / (((c : ℂ) + t * Complex.I) - 1)) *
              (∫ x : ℝ,
                K x *
                  Complex.exp
                    (Complex.I * (t : ℂ) * (x : ℂ)) *
                  Complex.exp (((c - 1 : ℝ) : ℂ) * (x : ℂ))))) :=
    fixedRightLine_fourierCauchy_symmetricTruncation_tendsto_fullLine
      K hK_cont hK_compact hK_smooth c hc
  have hvalue :
      (∫ t : ℝ,
          (-1 / (((c : ℂ) + t * Complex.I) - 1)) *
            (∫ x : ℝ,
              K x *
                Complex.exp
                  (Complex.I * (t : ℂ) * (x : ℂ)) *
                Complex.exp (((c - 1 : ℝ) : ℂ) * (x : ℂ)))) =
        ∫ x in Set.Ici (0 : ℝ),
          (-2 * (Real.pi : ℂ)) * K x :=
    fixedRightLine_fourierCauchy_fullLine_smooth_oneSidedProjection
      K hK_cont hK_compact hK_smooth c hc
  exact hvalue ▸ hfull

/-- Generic one-sided Fourier-Cauchy inversion for a smooth compactly supported
time-side kernel on the fixed right line. -/
theorem fixedRightLine_fourierCauchy_fullLine_oneSidedProjection
    (K : ℝ → ℂ) (hK_cont : Continuous K) (hK_compact : HasCompactSupport K)
    (hK_smooth : ContDiff ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) K)
    (c : ℝ) (hc : 1 < c) :
    (∫ t : ℝ,
        (-1 / (((c : ℂ) + t * Complex.I) - 1)) *
          (∫ x : ℝ,
            K x *
              Complex.exp
                (Complex.I * (t : ℂ) * (x : ℂ)) *
              Complex.exp (((c - 1 : ℝ) : ℂ) * (x : ℂ)))) =
      ∫ x in Set.Ici (0 : ℝ),
        (-2 * (Real.pi : ℂ)) * K x := by
  exact
    fixedRightLine_fourierCauchy_fullLine_smooth_oneSidedProjection
      K hK_cont hK_compact hK_smooth c hc

/-- Full-line Cauchy inversion after the vertical slice has already been
rewritten as the Fourier transform of the right projection kernel. -/
theorem zetaLaplaceTransform_rightOnePoleProjectionKernel_fullLineCauchyValue_fourierKernel
    (f : LFunctions.ZetaAdmissibleFunction) (c : ℝ) (hc : 1 < c) :
    (∫ t : ℝ,
        (-1 / (((c : ℂ) + t * Complex.I) - 1)) *
          (∫ x : ℝ,
            zetaLaplaceTransform_rightOnePoleProjectionKernel f.toZetaTestFunction' x *
              Complex.exp
                (Complex.I * (t : ℂ) * (x : ℂ)) *
              Complex.exp (((c - 1 : ℝ) : ℂ) * (x : ℂ)))) =
      zetaLaplaceTransform_rightOnePoleCauchyProjectionValue f.toZetaTestFunction' c := by
  calc
    (∫ t : ℝ,
        (-1 / (((c : ℂ) + t * Complex.I) - 1)) *
          (∫ x : ℝ,
            zetaLaplaceTransform_rightOnePoleProjectionKernel f.toZetaTestFunction' x *
              Complex.exp
                (Complex.I * (t : ℂ) * (x : ℂ)) *
              Complex.exp (((c - 1 : ℝ) : ℂ) * (x : ℂ))))
        =
        ∫ x in Set.Ici (0 : ℝ),
          (-2 * (Real.pi : ℂ)) *
            zetaLaplaceTransform_rightOnePoleProjectionKernel f.toZetaTestFunction' x :=
          fixedRightLine_fourierCauchy_fullLine_oneSidedProjection
            (zetaLaplaceTransform_rightOnePoleProjectionKernel f.toZetaTestFunction')
            (zetaLaplaceTransform_rightOnePoleProjectionKernel_continuous f.toZetaTestFunction')
            (zetaLaplaceTransform_rightOnePoleProjectionKernel_hasCompactSupport f.toZetaTestFunction')
            (zetaLaplaceTransform_rightOnePoleProjectionKernel_contDiff_admissible f)
            c hc
    _ = zetaLaplaceTransform_rightOnePoleCauchyProjectionValue f.toZetaTestFunction' c := by
          unfold zetaLaplaceTransform_rightOnePoleCauchyProjectionValue
          unfold zetaLaplaceTransform_rightOnePoleProjectionKernel
          exact
            setIntegral_congr_fun measurableSet_Ici
              (fun x _hx =>
                (mul_assoc
                  (-2 * (Real.pi : ℂ))
                  (f.toZetaTestFunction' x)
                  (Complex.exp ((1 / 2 : ℂ) * (x : ℂ)))).symm)

/-- One-sided Cauchy inversion for the right projection kernel on the fixed
line.

This is the genuine analytic core: the full-line Fourier-Cauchy multiplier
integral recovers the positive-time half-line projection value. -/
theorem zetaLaplaceTransform_rightOnePoleProjectionKernel_fullLineCauchyValue
    (f : LFunctions.ZetaAdmissibleFunction) (c : ℝ) (hc : 1 < c) :
    (∫ t : ℝ,
        (-1 / (((c : ℂ) + t * Complex.I) - 1)) *
          zetaLaplaceTransform f.toZetaTestFunction'
            (((c : ℂ) + t * Complex.I) - 1 / 2)) =
      zetaLaplaceTransform_rightOnePoleCauchyProjectionValue f.toZetaTestFunction' c := by
  calc
    (∫ t : ℝ,
        (-1 / (((c : ℂ) + t * Complex.I) - 1)) *
          zetaLaplaceTransform f.toZetaTestFunction'
            (((c : ℂ) + t * Complex.I) - 1 / 2))
        =
        ∫ t : ℝ,
          (-1 / (((c : ℂ) + t * Complex.I) - 1)) *
            (∫ x : ℝ,
              zetaLaplaceTransform_rightOnePoleProjectionKernel f.toZetaTestFunction' x *
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
                      f.toZetaTestFunction' c t)))
    _ = zetaLaplaceTransform_rightOnePoleCauchyProjectionValue f.toZetaTestFunction' c :=
          zetaLaplaceTransform_rightOnePoleProjectionKernel_fullLineCauchyValue_fourierKernel
            f c hc

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
`((c - 1) + it)⁻¹` projects onto the positive time half-line with an
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
                  f c hc
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
