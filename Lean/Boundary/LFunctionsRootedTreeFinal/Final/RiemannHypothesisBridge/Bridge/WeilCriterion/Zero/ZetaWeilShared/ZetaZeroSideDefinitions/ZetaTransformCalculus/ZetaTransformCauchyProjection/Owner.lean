import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaTransformCalculus.ZetaTransformCalculusBase.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaAdmissibleSpectralInterpolation.ZetaAdmissiblePaleyWiener.IteratedOscillatoryKernel.Owner
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
  sorry

/-- The upper semicircle correction term vanishes for positive time. -/
theorem scalarFourierLaplacePlemelj_positiveUpperArc_tendsto_zero
    (a : ℝ) (ha : 0 < a) (x : ℝ) (hx : x ∈ Set.Ioi (0 : ℝ)) :
    Tendsto
      (fun T : ℝ => scalarFourierLaplacePlemelj_positiveUpperArc a x T)
      atTop
      (𝓝 0) := by
  sorry

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
  sorry

/-- The lower semicircle correction term vanishes for negative time. -/
theorem scalarFourierLaplacePlemelj_negativeLowerArc_tendsto_zero
    (a : ℝ) (ha : 0 < a) (x : ℝ) (hx : x < 0) :
    Tendsto
      (fun T : ℝ => scalarFourierLaplacePlemelj_negativeLowerArc a x T)
      atTop
      (𝓝 0) := by
  sorry

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

/-- Positive-time uniform finite-window bound for the normalized scalar Cauchy
kernel. -/
theorem scalarFourierLaplacePlemelj_unweighted_window_mul_exp_uniform_bound_positive
    (a : ℝ) (ha : 0 < a) (T x : ℝ) (hx : 0 < x) :
    ‖(∫ t in Set.Icc (-T) T,
      (-1 / ((a : ℂ) + t * Complex.I)) *
        Complex.exp
          (Complex.I * (t : ℂ) * (x : ℂ))) *
        Complex.exp ((a : ℂ) * (x : ℂ))‖
      ≤ 2 * (Real.pi + 1) := by
  sorry

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

/-- Negative-time uniform finite-window bound for the normalized scalar Cauchy
kernel. -/
theorem scalarFourierLaplacePlemelj_unweighted_window_mul_exp_uniform_bound_negative
    (a : ℝ) (ha : 0 < a) (T x : ℝ) (hx : x < 0) :
    ‖(∫ t in Set.Icc (-T) T,
      (-1 / ((a : ℂ) + t * Complex.I)) *
        Complex.exp
          (Complex.I * (t : ℂ) * (x : ℂ))) *
        Complex.exp ((a : ℂ) * (x : ℂ))‖
      ≤ 2 * (Real.pi + 1) := by
  sorry

/-- Uniform finite-window bound for the normalized scalar Cauchy kernel after
the compensating exponential has been included. -/
theorem scalarFourierLaplacePlemelj_unweighted_window_mul_exp_uniform_bound
    (a : ℝ) (ha : 0 < a) (T x : ℝ) :
    ‖(∫ t in Set.Icc (-T) T,
      (-1 / ((a : ℂ) + t * Complex.I)) *
        Complex.exp
          (Complex.I * (t : ℂ) * (x : ℂ))) *
        Complex.exp ((a : ℂ) * (x : ℂ))‖
      ≤ 2 * (Real.pi + 1) := by
  match lt_trichotomy x 0 with
  | Or.inl hxneg =>
      exact
        scalarFourierLaplacePlemelj_unweighted_window_mul_exp_uniform_bound_negative
          a ha T x hxneg
  | Or.inr hnotneg =>
      match hnotneg with
      | Or.inl hxzero =>
          exact
            scalarFourierLaplacePlemelj_unweighted_window_mul_exp_uniform_bound_zero
              a ha T x hxzero
      | Or.inr hxpos =>
          exact
            scalarFourierLaplacePlemelj_unweighted_window_mul_exp_uniform_bound_positive
              a ha T x hxpos

/-- Uniform finite-window bound for the normalized Fourier-Laplace Plemelj
kernel. -/
theorem scalarFourierLaplacePlemelj_uniform_bound
    (a : ℝ) (ha : 0 < a) (T x : ℝ) :
    ‖(∫ t in Set.Icc (-T) T,
      (-1 / ((a : ℂ) + t * Complex.I)) *
        Complex.exp
          (Complex.I * (t : ℂ) * (x : ℂ)) *
        Complex.exp ((a : ℂ) * (x : ℂ)))‖
      ≤ 2 * (Real.pi + 1) := by
  exact Eq.subst
    (motive := fun z : ℂ => ‖z‖ ≤ 2 * (Real.pi + 1))
    (scalarFourierLaplacePlemelj_positive_window_mul_exp_eq_window_with_exp
      a x T)
    (scalarFourierLaplacePlemelj_unweighted_window_mul_exp_uniform_bound
      a ha T x)

/-- Normalized scalar Fourier-Laplace Plemelj package.

For `a > 0`, the symmetric Fourier windows of
`-exp(a x)/(a + i t)` converge to the open half-line multiplier and obey the
uniform scalar bound needed for dominated convergence. -/
theorem scalarFourierLaplacePlemelj_openHalfLine_and_uniform_bound
    (a : ℝ) (ha : 0 < a) :
    (∀ x : ℝ, x ≠ 0 →
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
            (fun _ : ℝ => (-2 * (Real.pi : ℂ))) x))) ∧
    (∀ T x : ℝ,
      ‖(∫ t in Set.Icc (-T) T,
        (-1 / ((a : ℂ) + t * Complex.I)) *
          Complex.exp
            (Complex.I * (t : ℂ) * (x : ℂ)) *
          Complex.exp ((a : ℂ) * (x : ℂ)))‖
        ≤ 2 * (Real.pi + 1)) := by
  exact
    ⟨fun x hx0 =>
      scalarFourierLaplacePlemelj_pointwise_openHalfLine a ha x hx0,
     fun T x =>
      scalarFourierLaplacePlemelj_uniform_bound a ha T x⟩

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
open-half-line multiplier and are uniformly bounded by the scalar Plemelj
constant. -/
theorem fixedRightLine_scalarCauchyWindow_plemelj_openHalfLine_and_uniform_bound
    (c : ℝ) (hc : 1 < c) :
    (∀ x : ℝ, x ≠ 0 →
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
            (fun _ : ℝ => (-2 * (Real.pi : ℂ))) x))) ∧
    (∀ T x : ℝ,
      ‖(∫ t in Set.Icc (-T) T,
        (-1 / (((c : ℂ) + t * Complex.I) - 1)) *
          Complex.exp
            (Complex.I * (t : ℂ) * (x : ℂ)) *
          Complex.exp (((c - 1 : ℝ) : ℂ) * (x : ℂ)))‖
        ≤ 2 * (Real.pi + 1)) := by
  have ha : 0 < c - 1 :=
    sub_pos.mpr hc
  have hbase :=
    scalarFourierLaplacePlemelj_openHalfLine_and_uniform_bound
      (c - 1) ha
  constructor
  · intro x
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
      (hbase.1 x hx0)
  · intro T x
    have hwindow :=
      fixedRightLine_scalarCauchyWindow_eq_normalizedLaplaceWindow c x T
    exact Eq.subst
      (motive := fun z : ℂ => ‖z‖ ≤ 2 * (Real.pi + 1))
      hwindow.symm
      (hbase.2 T x)

/-- Scalar fixed-right-line Plemelj theorem for finite symmetric Cauchy
windows, including the open half-line limit and the uniform scalar bound
needed for dominated convergence. -/
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
    (fixedRightLine_scalarCauchyWindow_plemelj_openHalfLine_and_uniform_bound
      c hc).1 x hx0

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

/-- Uniform scalar bound component of the fixed-right-line Plemelj theorem. -/
theorem fixedRightLine_scalarCauchyWindow_uniform_norm_bound_from_plemelj
    (c : ℝ) (hc : 1 < c) (T x : ℝ) :
    ‖(∫ t in Set.Icc (-T) T,
      (-1 / (((c : ℂ) + t * Complex.I) - 1)) *
        Complex.exp
          (Complex.I * (t : ℂ) * (x : ℂ)) *
        Complex.exp (((c - 1 : ℝ) : ℂ) * (x : ℂ)))‖
      ≤ 2 * (Real.pi + 1) := by
  exact
    (fixedRightLine_scalarCauchyWindow_plemelj_openHalfLine_and_uniform_bound
      c hc).2 T x

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

/-- Uniform scalar bound for the finite fixed-right-line Cauchy windows. -/
theorem fixedRightLine_scalarCauchyWindow_uniform_norm_bound
    (c : ℝ) (hc : 1 < c) :
    ∃ C : ℝ,
      0 ≤ C ∧
        ∀ᶠ T in atTop,
          ∀ x : ℝ,
            ‖(∫ t in Set.Icc (-T) T,
              (-1 / (((c : ℂ) + t * Complex.I) - 1)) *
                Complex.exp
                  (Complex.I * (t : ℂ) * (x : ℂ)) *
                Complex.exp (((c - 1 : ℝ) : ℂ) * (x : ℂ)))‖
              ≤ C := by
  refine ⟨2 * (Real.pi + 1), ?_, ?_⟩
  · exact mul_nonneg zero_le_two
      (add_nonneg Real.pi_nonneg zero_le_one)
  · exact Eventually.of_forall
      (fun T : ℝ =>
        fun x : ℝ =>
          fixedRightLine_scalarCauchyWindow_uniform_norm_bound_from_plemelj
            c hc T x)

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
  match fixedRightLine_scalarCauchyWindow_uniform_norm_bound c hc with
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
      refine ⟨G, hG_integrable, hG_nonnegative, ?_⟩
      exact hC_eventual.mono
        (fun T hT =>
          Eventually.of_forall
            (fun x : ℝ =>
              calc
                ‖K x *
                  (∫ t in Set.Icc (-T) T,
                    (-1 / (((c : ℂ) + t * Complex.I) - 1)) *
                      Complex.exp
                        (Complex.I * (t : ℂ) * (x : ℂ)) *
                      Complex.exp (((c - 1 : ℝ) : ℂ) * (x : ℂ)))‖
                    =
                    ‖K x‖ *
                      ‖(∫ t in Set.Icc (-T) T,
                        (-1 / (((c : ℂ) + t * Complex.I) - 1)) *
                          Complex.exp
                            (Complex.I * (t : ℂ) * (x : ℂ)) *
                          Complex.exp (((c - 1 : ℝ) : ℂ) * (x : ℂ)))‖ := by
                      exact norm_mul (K x)
                        (∫ t in Set.Icc (-T) T,
                          (-1 / (((c : ℂ) + t * Complex.I) - 1)) *
                            Complex.exp
                              (Complex.I * (t : ℂ) * (x : ℂ)) *
                            Complex.exp (((c - 1 : ℝ) : ℂ) * (x : ℂ)))
                _ ≤ ‖K x‖ * C := by
                      exact mul_le_mul_of_nonneg_left (hT x)
                        (norm_nonneg (K x))
                _ = G x := by
                      exact (mul_comm ‖K x‖ C).trans rfl))

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
