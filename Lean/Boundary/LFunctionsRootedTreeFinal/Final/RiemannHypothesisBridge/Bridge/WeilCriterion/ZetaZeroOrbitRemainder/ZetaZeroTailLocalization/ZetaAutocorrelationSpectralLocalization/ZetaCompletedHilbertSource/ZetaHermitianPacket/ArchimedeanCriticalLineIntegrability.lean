import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaCompletedHilbertSource.ZetaHermitianPacket.ArchimedeanCriticalLineKernelBound
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# Integrability of the centered archimedean channel

The Binet main and remainder terms give measurable quarter-line Gamma data.
The linear kernel bound then combines with admissible Paley-Wiener decay.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open Complex
open MeasureTheory

namespace ZetaAdmissibleFunction

/-- The ordinary Gamma logarithmic derivative is strongly measurable on the
positive quarter-line. -/
theorem zetaCompletedQuarterLineGammaLogDerivative_aestronglyMeasurable :
    AEStronglyMeasurable
      (fun u : ℝ =>
        deriv Complex.Gamma ((1 / 4 : ℝ) + u * Complex.I) /
          Complex.Gamma ((1 / 4 : ℝ) + u * Complex.I))
      (volume : Measure ℝ) := by
  have mainMeasurable :=
    Complex.GammaLogDerivativeFixedVerticalMain_aestronglyMeasurable
      (1 / 4 : ℝ)
  have remainderMeasurable :=
    Complex.GammaLogDerivativeFixedVerticalRemainder_aestronglyMeasurable
      (1 / 4 : ℝ)
  have sumMeasurable := mainMeasurable.add remainderMeasurable
  have quarterPositive : (0 : ℝ) < (1 / 4 : ℝ) :=
    div_pos zero_lt_one zero_lt_four
  have equality :
      ∀ u : ℝ,
        deriv Complex.Gamma ((1 / 4 : ℝ) + u * Complex.I) /
            Complex.Gamma ((1 / 4 : ℝ) + u * Complex.I) =
          Complex.GammaLogDerivativeFixedVerticalMain (1 / 4 : ℝ) u +
            Complex.GammaLogDerivativeFixedVerticalRemainder (1 / 4 : ℝ) u :=
    fun u : ℝ =>
      Complex.Gamma_logDerivative_fixedRealPartLine_eq_main_add_remainder_direct
        quarterPositive u
  exact sumMeasurable.congr
    (Filter.Eventually.of_forall (fun u : ℝ => (equality u).symm))

/-- The quarter-line Gamma logarithmic derivative remains strongly measurable
after the nonsingular height rescaling `t ↦ t / 2`. -/
theorem zetaCompletedQuarterLineGammaLogDerivative_halfHeight_aestronglyMeasurable :
    AEStronglyMeasurable
      (fun t : ℝ =>
        deriv Complex.Gamma
            ((1 / 4 : ℝ) + (t / 2 : ℝ) * Complex.I) /
          Complex.Gamma
            ((1 / 4 : ℝ) + (t / 2 : ℝ) * Complex.I))
      (volume : Measure ℝ) := by
  let base : ℝ → ℂ :=
    fun u : ℝ =>
      deriv Complex.Gamma ((1 / 4 : ℝ) + u * Complex.I) /
        Complex.Gamma ((1 / 4 : ℝ) + u * Complex.I)
  let scale : ℝ → ℝ := fun t : ℝ => (1 / 2 : ℝ) • t
  have halfNonzero : (1 / 2 : ℝ) ≠ 0 :=
    ne_of_gt one_half_pos
  have scaleQuasi :
      Measure.QuasiMeasurePreserving scale (volume : Measure ℝ) volume :=
    Measure.quasiMeasurePreserving_smul
      (E := ℝ) (μ := volume) halfNonzero
  have compositionMeasurable :
      AEStronglyMeasurable (base ∘ scale) (volume : Measure ℝ) :=
    zetaCompletedQuarterLineGammaLogDerivative_aestronglyMeasurable.comp_quasiMeasurePreserving
      scaleQuasi
  have functionEquality :
      (base ∘ scale) =
        fun t : ℝ =>
          deriv Complex.Gamma
              ((1 / 4 : ℝ) + (t / 2 : ℝ) * Complex.I) /
            Complex.Gamma
              ((1 / 4 : ℝ) + (t / 2 : ℝ) * Complex.I) := by
    funext t
    have scaleEquality : scale t = t / 2 := by
      have scaleToProduct :
          scale t = (1 / 2 : ℝ) * t := by
        rfl
      have productCommuted :
          (1 / 2 : ℝ) * t = t * (1 / 2 : ℝ) :=
        mul_comm (1 / 2 : ℝ) t
      have halfToInverse :
          (1 / 2 : ℝ) = (2 : ℝ)⁻¹ :=
        one_div 2
      have productToDivision :
          t * (1 / 2 : ℝ) = t / 2 := by
        exact Eq.trans
          (congrArg (fun factor : ℝ => t * factor) halfToInverse)
          (div_eq_mul_inv t 2).symm
      exact Eq.trans scaleToProduct
        (Eq.trans productCommuted productToDivision)
    exact congrArg base scaleEquality
  exact Eq.subst
    (motive := fun function : ℝ → ℂ =>
      AEStronglyMeasurable function (volume : Measure ℝ))
    functionEquality
    compositionMeasurable

/-- The half-weighted quarter-line Gamma term is strongly measurable. -/
theorem zetaCompletedQuarterLineHalfGammaLogDerivative_aestronglyMeasurable :
    AEStronglyMeasurable
      (fun t : ℝ =>
        (deriv Complex.Gamma
            ((1 / 4 : ℝ) + (t / 2 : ℝ) * Complex.I) * (1 / 2 : ℂ)) /
          Complex.Gamma
            ((1 / 4 : ℝ) + (t / 2 : ℝ) * Complex.I))
      (volume : Measure ℝ) := by
  have baseMeasurable :=
    zetaCompletedQuarterLineGammaLogDerivative_halfHeight_aestronglyMeasurable
  have multipliedMeasurable := baseMeasurable.mul_const (1 / 2 : ℂ)
  have functionEquality :
      (fun t : ℝ =>
        (deriv Complex.Gamma
            ((1 / 4 : ℝ) + (t / 2 : ℝ) * Complex.I) /
          Complex.Gamma
            ((1 / 4 : ℝ) + (t / 2 : ℝ) * Complex.I)) * (1 / 2 : ℂ)) =
        fun t : ℝ =>
          (deriv Complex.Gamma
              ((1 / 4 : ℝ) + (t / 2 : ℝ) * Complex.I) * (1 / 2 : ℂ)) /
            Complex.Gamma
              ((1 / 4 : ℝ) + (t / 2 : ℝ) * Complex.I) := by
    funext t
    exact (mul_div_right_comm
      (deriv Complex.Gamma
        ((1 / 4 : ℝ) + (t / 2 : ℝ) * Complex.I))
      (1 / 2 : ℂ)
      (Complex.Gamma
        ((1 / 4 : ℝ) + (t / 2 : ℝ) * Complex.I))).symm
  exact Eq.subst
    (motive := fun function : ℝ → ℂ =>
      AEStronglyMeasurable function (volume : Measure ℝ))
    functionEquality
    multipliedMeasurable

/-- The `Gammaℝ` logarithmic derivative is strongly measurable on the
centered critical line. -/
theorem zetaCompletedCenteredGammaRealLogDerivative_aestronglyMeasurable :
    AEStronglyMeasurable
      (fun t : ℝ =>
        deriv Complex.Gammaℝ (zetaCompletedCenteredSpectralLine t) /
          Complex.Gammaℝ (zetaCompletedCenteredSpectralLine t))
      (volume : Measure ℝ) := by
  have rightMeasurable :=
    (aestronglyMeasurable_const :
      AEStronglyMeasurable
        (fun _ : ℝ =>
          Complex.log (Real.pi : ℂ) * (-(1 / 2 : ℂ)))
        (volume : Measure ℝ)).add
      zetaCompletedQuarterLineHalfGammaLogDerivative_aestronglyMeasurable
  have equality :
      ∀ t : ℝ,
        deriv Complex.Gammaℝ (zetaCompletedCenteredSpectralLine t) /
            Complex.Gammaℝ (zetaCompletedCenteredSpectralLine t) =
          Complex.log (Real.pi : ℂ) * (-(1 / 2 : ℂ)) +
            (deriv Complex.Gamma
                ((1 / 4 : ℝ) + (t / 2 : ℝ) * Complex.I) * (1 / 2 : ℂ)) /
              Complex.Gamma
                ((1 / 4 : ℝ) + (t / 2 : ℝ) * Complex.I) :=
    GammaReal_logDerivative_centeredSpectralLine_eq_quarterLine
  exact rightMeasurable.congr
    (Filter.Eventually.of_forall (fun t : ℝ => (equality t).symm))

/-- The inverse-Gamma completion logarithmic derivative is strongly measurable
on the centered critical line. -/
theorem inverseGammaCompletionLogDeriv_centered_aestronglyMeasurable :
    AEStronglyMeasurable
      (fun t : ℝ =>
        inverseGammaCompletionLogDeriv
          (zetaCompletedCenteredSpectralLine t))
      (volume : Measure ℝ) := by
  have negativeMeasurable :=
    zetaCompletedCenteredGammaRealLogDerivative_aestronglyMeasurable.neg
  have equality :
      ∀ t : ℝ,
        inverseGammaCompletionLogDeriv
            (zetaCompletedCenteredSpectralLine t) =
          -(deriv Complex.Gammaℝ (zetaCompletedCenteredSpectralLine t) /
            Complex.Gammaℝ (zetaCompletedCenteredSpectralLine t)) := by
    intro t
    exact Eq.trans
      (inverseGammaCompletionLogDeriv_centeredSpectralLine_eq t)
      (neg_div
        (Complex.Gammaℝ (zetaCompletedCenteredSpectralLine t))
        (deriv Complex.Gammaℝ (zetaCompletedCenteredSpectralLine t)))
  exact negativeMeasurable.congr
    (Filter.Eventually.of_forall (fun t : ℝ => (equality t).symm))

/-- The elementary centered pole correction is strongly measurable. -/
theorem zetaCompletedCenteredElementaryPoleCorrection_aestronglyMeasurable :
    AEStronglyMeasurable
      (fun t : ℝ =>
        (-1 : ℂ) / zetaCompletedCenteredSpectralLine t -
          1 / (zetaCompletedCenteredSpectralLine t - 1))
      (volume : Measure ℝ) := by
  have lineMeasurable :
      Measurable (fun t : ℝ => zetaCompletedCenteredSpectralLine t) :=
    have imaginaryCoordinateMeasurable :
        Measurable (fun t : ℝ => (t : ℂ)) :=
      Complex.measurable_ofReal.comp measurable_id
    have imaginaryTermMeasurable :
        Measurable (fun t : ℝ => (t : ℂ) * Complex.I) :=
      imaginaryCoordinateMeasurable.mul measurable_const
    measurable_const.add imaginaryTermMeasurable
  have firstMeasurable :
      Measurable
        (fun t : ℝ => (-1 : ℂ) / zetaCompletedCenteredSpectralLine t) :=
    measurable_const.div lineMeasurable
  have secondDenominatorMeasurable :
      Measurable
        (fun t : ℝ => zetaCompletedCenteredSpectralLine t - 1) :=
    lineMeasurable.sub measurable_const
  have secondMeasurable :
      Measurable
        (fun t : ℝ => 1 / (zetaCompletedCenteredSpectralLine t - 1)) :=
    measurable_const.div secondDenominatorMeasurable
  exact (firstMeasurable.sub secondMeasurable).aestronglyMeasurable

/-- The centered archimedean logarithmic-derivative kernel is strongly
measurable. -/
theorem zetaCompletedArchimedeanLogDerivativeKernel_centered_aestronglyMeasurable :
    AEStronglyMeasurable
      (fun t : ℝ =>
        zetaCompletedArchimedeanLogDerivativeKernel
          (zetaCompletedCenteredSpectralLine t))
      (volume : Measure ℝ) := by
  have differenceMeasurable :=
    inverseGammaCompletionLogDeriv_centered_aestronglyMeasurable.sub
      zetaCompletedCenteredElementaryPoleCorrection_aestronglyMeasurable
  exact differenceMeasurable

/-- The centered archimedean channel is integrable for every admissible
probe. -/
theorem zetaCompletedArchimedeanCenteredIntegrand_integrable
    (f : ZetaAdmissibleFunction) :
    Integrable (zetaCompletedArchimedeanCenteredIntegrand f)
      (volume : Measure ℝ) := by
  exact zetaCompletedCriticalLineProduct_integrable_of_linearFactor
    f
    (fun t : ℝ =>
      zetaCompletedArchimedeanLogDerivativeKernel
        (zetaCompletedCenteredSpectralLine t))
    zetaCompletedArchimedeanKernelLinearBoundConstant
    zetaCompletedArchimedeanKernelLinearBoundConstant_nonneg
    zetaCompletedArchimedeanLogDerivativeKernel_centered_aestronglyMeasurable
    zetaCompletedArchimedeanLogDerivativeKernel_centered_bound

/-- The Hermitian critical-line archimedean kernel is strongly measurable. -/
theorem zetaCompletedArchimedeanHermitianKernel_aestronglyMeasurable :
    AEStronglyMeasurable zetaCompletedArchimedeanHermitianKernel
      (volume : Measure ℝ) := by
  let kernel : ℝ → ℂ := fun t : ℝ =>
    zetaCompletedArchimedeanLogDerivativeKernel
      (zetaCompletedCenteredSpectralLine t)
  have kernelMeasurable :
      AEStronglyMeasurable kernel (volume : Measure ℝ) :=
    zetaCompletedArchimedeanLogDerivativeKernel_centered_aestronglyMeasurable
  have conjugateMeasurable :
      AEStronglyMeasurable
        (fun t : ℝ => star (kernel t))
        (volume : Measure ℝ) :=
    continuous_star.comp_aestronglyMeasurable kernelMeasurable
  have sumMeasurable :
      AEStronglyMeasurable
        (fun t : ℝ => kernel t + star (kernel t))
        (volume : Measure ℝ) :=
    kernelMeasurable.add conjugateMeasurable
  exact Eq.subst
    (motive := fun candidate : ℝ → ℂ =>
      AEStronglyMeasurable candidate (volume : Measure ℝ))
    (funext (fun t : ℝ => Eq.refl _)).symm
    sumMeasurable

/-- The Hermitian critical-line kernel inherits an explicit linear bound. -/
theorem zetaCompletedArchimedeanHermitianKernel_centered_bound
    (t : ℝ) :
    ‖zetaCompletedArchimedeanHermitianKernel t‖ ≤
      (2 * zetaCompletedArchimedeanKernelLinearBoundConstant) *
        (1 + ‖t‖) := by
  let kernel : ℂ :=
    zetaCompletedArchimedeanLogDerivativeKernel
      (zetaCompletedCenteredSpectralLine t)
  let bound : ℝ :=
    zetaCompletedArchimedeanKernelLinearBoundConstant * (1 + ‖t‖)
  have kernelBound : ‖kernel‖ ≤ bound :=
    zetaCompletedArchimedeanLogDerivativeKernel_centered_bound t
  have conjugateNorm : ‖star kernel‖ = ‖kernel‖ :=
    norm_star kernel
  have conjugateBound : ‖star kernel‖ ≤ bound :=
    Eq.subst
      (motive := fun value : ℝ => value ≤ bound)
      conjugateNorm.symm
      kernelBound
  have sumBound : ‖kernel + star kernel‖ ≤ bound + bound :=
    le_trans (norm_add_le kernel (star kernel))
      (add_le_add kernelBound conjugateBound)
  have doubleBound :
      bound + bound =
        (2 * zetaCompletedArchimedeanKernelLinearBoundConstant) *
          (1 + ‖t‖) := by
    calc
      bound + bound = 2 * bound := by
        exact (two_mul bound).symm
      _ = (2 * zetaCompletedArchimedeanKernelLinearBoundConstant) *
          (1 + ‖t‖) := by
        exact (mul_assoc 2
          zetaCompletedArchimedeanKernelLinearBoundConstant
          (1 + ‖t‖)).symm
  exact sumBound.trans_eq doubleBound

/-- The Hermitian archimedean channel is integrable for every admissible
probe. -/
theorem zetaCompletedArchimedeanHermitianIntegrand_integrable
    (f : ZetaAdmissibleFunction) :
    Integrable (zetaCompletedArchimedeanHermitianIntegrand f)
      (volume : Measure ℝ) := by
  exact zetaCompletedCriticalLineProduct_integrable_of_linearFactor
    f
    zetaCompletedArchimedeanHermitianKernel
    (2 * zetaCompletedArchimedeanKernelLinearBoundConstant)
    (mul_nonneg zero_le_two
      zetaCompletedArchimedeanKernelLinearBoundConstant_nonneg)
    zetaCompletedArchimedeanHermitianKernel_aestronglyMeasurable
    zetaCompletedArchimedeanHermitianKernel_centered_bound

/-- The signed packet form is unconditionally the real archimedean
autocorrelation contribution. -/
theorem zetaCompletedArchimedeanSignedQuadraticForm_eq_archimedeanContribution_re_owner
    (f : ZetaAdmissibleFunction) :
    zetaCompletedArchimedeanSignedQuadraticForm f =
      (Complex.re
        (zetaCompletedExplicitFormulaArchimedeanContribution
          (convolutionAutocorrelation f)) : ℂ) := by
  exact
    zetaCompletedArchimedeanSignedQuadraticForm_eq_archimedeanContribution_re
      f
      (zetaCompletedArchimedeanHermitianIntegrand_integrable
        (convolutionAutocorrelation f))

/-- The real signed archimedean weight is strongly measurable. -/
theorem zetaCompletedArchimedeanSignedWeight_aestronglyMeasurable :
    AEStronglyMeasurable zetaCompletedArchimedeanSignedWeight
      (volume : Measure ℝ) := by
  exact Complex.continuous_re.comp_aestronglyMeasurable
    zetaCompletedArchimedeanHermitianKernel_aestronglyMeasurable

/-- The positive variation of the archimedean weight is strongly measurable. -/
theorem zetaCompletedArchimedeanPositiveWeight_aestronglyMeasurable :
    AEStronglyMeasurable zetaCompletedArchimedeanPositiveWeight
      (volume : Measure ℝ) := by
  exact (continuous_id.max continuous_const).comp_aestronglyMeasurable
    zetaCompletedArchimedeanSignedWeight_aestronglyMeasurable

/-- The negative variation of the archimedean weight is strongly measurable. -/
theorem zetaCompletedArchimedeanNegativeWeight_aestronglyMeasurable :
    AEStronglyMeasurable zetaCompletedArchimedeanNegativeWeight
      (volume : Measure ℝ) := by
  have negativeMeasurable :=
    zetaCompletedArchimedeanSignedWeight_aestronglyMeasurable.neg
  exact (continuous_id.max continuous_const).comp_aestronglyMeasurable
    negativeMeasurable

/-- The positive variation is bounded by the norm of the complex
archimedean kernel. -/
theorem zetaCompletedArchimedeanPositiveWeight_le_kernel_norm (t : ℝ) :
    zetaCompletedArchimedeanPositiveWeight t ≤
      ‖zetaCompletedArchimedeanHermitianKernel t‖ := by
  let kernel : ℂ := zetaCompletedArchimedeanHermitianKernel t
  have weightToAbsolute :
      max kernel.re 0 ≤ |kernel.re| :=
    max_le (le_abs_self kernel.re) (abs_nonneg kernel.re)
  have absoluteToNorm : |kernel.re| ≤ ‖kernel‖ :=
    RCLike.abs_re_le_norm kernel
  exact weightToAbsolute.trans absoluteToNorm

/-- The negative variation is bounded by the norm of the complex
archimedean kernel. -/
theorem zetaCompletedArchimedeanNegativeWeight_le_kernel_norm (t : ℝ) :
    zetaCompletedArchimedeanNegativeWeight t ≤
      ‖zetaCompletedArchimedeanHermitianKernel t‖ := by
  let kernel : ℂ := zetaCompletedArchimedeanHermitianKernel t
  have weightToAbsolute :
      max (-kernel.re) 0 ≤ |kernel.re| :=
    max_le (neg_le_abs kernel.re) (abs_nonneg kernel.re)
  have absoluteToNorm : |kernel.re| ≤ ‖kernel‖ :=
    RCLike.abs_re_le_norm kernel
  exact weightToAbsolute.trans absoluteToNorm

/-- The complex positive-weight factor has the common linear kernel bound. -/
theorem zetaCompletedArchimedeanPositiveWeight_complex_bound (t : ℝ) :
    ‖(zetaCompletedArchimedeanPositiveWeight t : ℂ)‖ ≤
      (2 * zetaCompletedArchimedeanKernelLinearBoundConstant) *
        (1 + ‖t‖) := by
  have weightNonnegative :
      0 ≤ zetaCompletedArchimedeanPositiveWeight t :=
    le_max_right _ _
  have normEquality :
      ‖(zetaCompletedArchimedeanPositiveWeight t : ℂ)‖ =
        zetaCompletedArchimedeanPositiveWeight t := by
    exact Eq.trans
      (RCLike.norm_ofReal (K := ℂ)
        (zetaCompletedArchimedeanPositiveWeight t))
      (abs_of_nonneg weightNonnegative)
  exact Eq.subst
    (motive := fun value : ℝ =>
      value ≤
        (2 * zetaCompletedArchimedeanKernelLinearBoundConstant) *
          (1 + ‖t‖))
    normEquality.symm
    ((zetaCompletedArchimedeanPositiveWeight_le_kernel_norm t).trans
      (zetaCompletedArchimedeanHermitianKernel_centered_bound t))

/-- The complex negative-weight factor has the common linear kernel bound. -/
theorem zetaCompletedArchimedeanNegativeWeight_complex_bound (t : ℝ) :
    ‖(zetaCompletedArchimedeanNegativeWeight t : ℂ)‖ ≤
      (2 * zetaCompletedArchimedeanKernelLinearBoundConstant) *
        (1 + ‖t‖) := by
  have weightNonnegative :
      0 ≤ zetaCompletedArchimedeanNegativeWeight t :=
    le_max_right _ _
  have normEquality :
      ‖(zetaCompletedArchimedeanNegativeWeight t : ℂ)‖ =
        zetaCompletedArchimedeanNegativeWeight t := by
    exact Eq.trans
      (RCLike.norm_ofReal (K := ℂ)
        (zetaCompletedArchimedeanNegativeWeight t))
      (abs_of_nonneg weightNonnegative)
  exact Eq.subst
    (motive := fun value : ℝ =>
      value ≤
        (2 * zetaCompletedArchimedeanKernelLinearBoundConstant) *
          (1 + ‖t‖))
    normEquality.symm
    ((zetaCompletedArchimedeanNegativeWeight_le_kernel_norm t).trans
      (zetaCompletedArchimedeanHermitianKernel_centered_bound t))

/-- The positive archimedean Gram coordinate is integrable. -/
theorem zetaCompletedArchimedeanPositiveGramCoordinate_integrable
    (f : ZetaAdmissibleFunction) :
    Integrable (zetaCompletedArchimedeanPositiveGramCoordinate f)
      (volume : Measure ℝ) := by
  have factorMeasurable :
      AEStronglyMeasurable
        (fun t : ℝ => (zetaCompletedArchimedeanPositiveWeight t : ℂ))
        (volume : Measure ℝ) :=
    Complex.continuous_ofReal.comp_aestronglyMeasurable
      zetaCompletedArchimedeanPositiveWeight_aestronglyMeasurable
  have productIntegrable :=
    zetaCompletedCriticalLineProduct_integrable_of_linearFactor
      (convolutionAutocorrelation f)
      (fun t : ℝ => (zetaCompletedArchimedeanPositiveWeight t : ℂ))
      (2 * zetaCompletedArchimedeanKernelLinearBoundConstant)
      (mul_nonneg zero_le_two
        zetaCompletedArchimedeanKernelLinearBoundConstant_nonneg)
      factorMeasurable
      zetaCompletedArchimedeanPositiveWeight_complex_bound
  have functionEquality :
      (fun t : ℝ =>
        (zetaCompletedArchimedeanPositiveWeight t : ℂ) *
          zetaCompletedExplicitFormulaPhi
            (convolutionAutocorrelation f) ((t : ℂ) * Complex.I)) =
        zetaCompletedArchimedeanPositiveGramCoordinate f := by
    funext t
    exact congrArg
      (fun value : ℂ =>
        (zetaCompletedArchimedeanPositiveWeight t : ℂ) * value)
      (zetaCompletedExplicitFormulaPhi_convolutionAutocorrelation_imaginary
        f t)
  exact Eq.subst
    (motive := fun function : ℝ → ℂ =>
      Integrable function (volume : Measure ℝ))
    functionEquality
    productIntegrable

/-- The negative archimedean Gram coordinate is integrable. -/
theorem zetaCompletedArchimedeanNegativeGramCoordinate_integrable
    (f : ZetaAdmissibleFunction) :
    Integrable (zetaCompletedArchimedeanNegativeGramCoordinate f)
      (volume : Measure ℝ) := by
  have factorMeasurable :
      AEStronglyMeasurable
        (fun t : ℝ => (zetaCompletedArchimedeanNegativeWeight t : ℂ))
        (volume : Measure ℝ) :=
    Complex.continuous_ofReal.comp_aestronglyMeasurable
      zetaCompletedArchimedeanNegativeWeight_aestronglyMeasurable
  have productIntegrable :=
    zetaCompletedCriticalLineProduct_integrable_of_linearFactor
      (convolutionAutocorrelation f)
      (fun t : ℝ => (zetaCompletedArchimedeanNegativeWeight t : ℂ))
      (2 * zetaCompletedArchimedeanKernelLinearBoundConstant)
      (mul_nonneg zero_le_two
        zetaCompletedArchimedeanKernelLinearBoundConstant_nonneg)
      factorMeasurable
      zetaCompletedArchimedeanNegativeWeight_complex_bound
  have functionEquality :
      (fun t : ℝ =>
        (zetaCompletedArchimedeanNegativeWeight t : ℂ) *
          zetaCompletedExplicitFormulaPhi
            (convolutionAutocorrelation f) ((t : ℂ) * Complex.I)) =
        zetaCompletedArchimedeanNegativeGramCoordinate f := by
    funext t
    exact congrArg
      (fun value : ℂ =>
        (zetaCompletedArchimedeanNegativeWeight t : ℂ) * value)
      (zetaCompletedExplicitFormulaPhi_convolutionAutocorrelation_imaginary
        f t)
  exact Eq.subst
    (motive := fun function : ℝ → ℂ =>
      Integrable function (volume : Measure ℝ))
    functionEquality
    productIntegrable

/-- Unconditional Jordan decomposition of the signed archimedean packet. -/
theorem zetaCompletedArchimedeanSignedQuadraticForm_eq_positive_sub_negative_owner
    (f : ZetaAdmissibleFunction) :
    zetaCompletedArchimedeanSignedQuadraticForm f =
      zetaCompletedArchimedeanPositiveQuadraticForm f -
        zetaCompletedArchimedeanNegativeQuadraticForm f := by
  exact zetaCompletedArchimedeanSignedQuadraticForm_eq_positive_sub_negative
    f
    (zetaCompletedArchimedeanPositiveGramCoordinate_integrable f)
    (zetaCompletedArchimedeanNegativeGramCoordinate_integrable f)

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
