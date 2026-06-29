import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.PaleyWienerMellinInversion
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.AffineKernelIntegrability
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.RealLineQuantitativeTails
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaAdmissibleSpectralInterpolation.ZetaAdmissiblePaleyWiener.Owner

/-!
# Fourier inversion hypotheses for Paley-Wiener sampling

This file owns the analytic regularity facts needed to apply the repository
Fourier inversion theorem to the horizontally twisted admissible time kernel.
The easy compact-support facts are discharged here; the remaining Fourier-side
integrability is the true Paley-Wiener decay obligation.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open Complex
open MeasureTheory
open scoped FourierTransform

namespace ZetaAdmissibleFunction

/-- The Mellin-inversion time kernel is the Paley-Wiener horizontal twist. -/
theorem zetaCompletedExplicitFormula_twistedTimeKernel_eq_horizontalTwist
    (f : ZetaAdmissibleFunction) (σ : ℝ) :
    (fun t : ℝ =>
        Complex.exp ((σ : ℂ) * (t : ℂ)) * f.toZetaTestFunction' t) =
      fun t : ℝ => zetaPaleyWienerHorizontalTwist f σ t := by
  funext t
  unfold zetaPaleyWienerHorizontalTwist
  have hmul :
      (σ : ℂ) * (t : ℂ) = ((σ * t : ℝ) : ℂ) :=
    (Complex.ofReal_mul σ t).symm
  have hexp :
      Complex.exp ((σ : ℂ) * (t : ℂ)) =
        (Real.exp (σ * t) : ℂ) :=
    Eq.trans
      (congrArg Complex.exp hmul)
      (Complex.ofReal_exp (σ * t)).symm
  calc
    Complex.exp ((σ : ℂ) * (t : ℂ)) * f.toZetaTestFunction' t =
        (Real.exp (σ * t) : ℂ) * f.toZetaTestFunction' t := by
      exact congrArg (fun z : ℂ => z * f.toZetaTestFunction' t) hexp
    _ = f.toZetaTestFunction' t * (Real.exp (σ * t) : ℂ) := by
      exact mul_comm (Real.exp (σ * t) : ℂ) (f.toZetaTestFunction' t)

/-- The horizontally twisted time kernel is integrable. -/
theorem zetaCompletedExplicitFormula_twistedTimeKernel_integrable
    (f : ZetaAdmissibleFunction) (σ : ℝ) :
    Integrable
      (fun t : ℝ =>
        Complex.exp ((σ : ℂ) * (t : ℂ)) * f.toZetaTestFunction' t) := by
  have htwist_integrable :
      Integrable (fun t : ℝ => zetaPaleyWienerHorizontalTwist f σ t) :=
    (zetaPaleyWienerHorizontalTwist_continuous f σ).integrable_of_hasCompactSupport
      (zetaPaleyWienerHorizontalTwist_hasCompactSupport f σ)
  exact Eq.subst
    (motive := fun g : ℝ → ℂ => Integrable g)
    (zetaCompletedExplicitFormula_twistedTimeKernel_eq_horizontalTwist f σ).symm
    htwist_integrable

/-- The horizontally twisted time kernel is continuous at every point. -/
theorem zetaCompletedExplicitFormula_twistedTimeKernel_continuousAt
    (f : ZetaAdmissibleFunction) (σ a : ℝ) :
    ContinuousAt
      (fun t : ℝ =>
        Complex.exp ((σ : ℂ) * (t : ℂ)) * f.toZetaTestFunction' t)
      a := by
  have htwist_continuousAt :
      ContinuousAt (fun t : ℝ => zetaPaleyWienerHorizontalTwist f σ t) a :=
    (zetaPaleyWienerHorizontalTwist_continuous f σ).continuousAt
  exact Eq.subst
    (motive := fun g : ℝ → ℂ => ContinuousAt g a)
    (zetaCompletedExplicitFormula_twistedTimeKernel_eq_horizontalTwist f σ).symm
    htwist_continuousAt

/-- The Fourier transform of the horizontally twisted time kernel is the
reflected vertical line of the Paley-Wiener transform. -/
theorem zetaCompletedExplicitFormula_twistedTimeKernel_fourier_eq_phi_reflected
    (f : ZetaAdmissibleFunction) (σ y : ℝ) :
    𝓕 (fun t : ℝ =>
        Complex.exp ((σ : ℂ) * (t : ℂ)) * f.toZetaTestFunction' t) y =
      zetaCompletedExplicitFormulaPhi f (σ + 2 * π * (-y) * I) := by
  exact
    (zetaCompletedExplicitFormulaPhi_verticalLine_eq_fourierIntegral_expTwist
      f σ (-y)).symm

/-- Re-coordinate the reflected vertical line used by the Fourier transform. -/
theorem zetaCompletedExplicitFormula_reflectedVerticalLine_re
    (σ y : ℝ) :
    ((σ : ℂ) + 2 * π * (-y) * I).re = σ := by
  calc
    ((σ : ℂ) + 2 * π * (-y) * I).re =
        (σ : ℂ).re + (2 * π * (-y) * I).re := by
      exact Complex.add_re (σ : ℂ) (2 * π * (-y) * I)
    _ = σ + (2 * π * (-y) * I).re := by
      exact congrArg (fun r : ℝ => r + (2 * π * (-y) * I).re)
        (Complex.ofReal_re σ)
    _ = σ + (-(2 * π * (-y) : ℂ).im) := by
      exact congrArg (fun r : ℝ => σ + r)
        (Complex.mul_I_re (2 * π * (-y) : ℂ))
    _ = σ + (-0) := by
      exact congrArg (fun r : ℝ => σ + (-r))
        (Complex.ofReal_im (2 * π * (-y)))
    _ = σ + 0 := by
      exact congrArg (fun r : ℝ => σ + r) (neg_zero : -(0 : ℝ) = 0)
    _ = σ := by
      exact add_zero σ

/-- Imaginary coordinate of the reflected vertical line used by the Fourier
transform. -/
theorem zetaCompletedExplicitFormula_reflectedVerticalLine_im
    (σ y : ℝ) :
    ((σ : ℂ) + 2 * π * (-y) * I).im = y * (-(2 * π)) := by
  calc
    ((σ : ℂ) + 2 * π * (-y) * I).im =
        0 + (2 * π * (-y) * I).im := by
      exact congrArg (fun r : ℝ => r + (2 * π * (-y) * I).im)
        (Complex.ofReal_im σ)
    _ = (2 * π * (-y) * I).im := by
      exact zero_add (2 * π * (-y) * I).im
    _ = (2 * π * (-y) : ℂ).re := by
      exact Complex.mul_I_im (2 * π * (-y) : ℂ)
    _ = 2 * π * (-y) := by
      exact Complex.ofReal_re (2 * π * (-y))
    _ = y * (-(2 * π)) := by
      exact Eq.trans
        (mul_neg (2 * π) y)
        (Eq.trans
          (congrArg Neg.neg (mul_comm (2 * π) y))
          (mul_neg y (2 * π)).symm)

/-- The fourth-order real-line majorant remains integrable after the vertical
Fourier-frequency scaling by `-2π`. -/
theorem zetaCompletedExplicitFormula_scaled_fourthOrderMajorant_integrable :
    Integrable
      (fun y : ℝ => (1 + ‖y * (-(2 * π))‖) ^ (-(4 : ℤ)))
      (volume : Measure ℝ) := by
  have hscale_ne : (-(2 * π) : ℝ) ≠ 0 :=
    neg_ne_zero.mpr (mul_ne_zero two_ne_zero Real.pi_ne_zero)
  exact realLine_integrable_one_add_norm_zpow_four.comp_mul_right' hscale_ne

/-- Paley-Wiener vertical-strip decay gives an integrable fourth-order
majorant for the reflected Fourier line. -/
theorem zetaCompletedExplicitFormula_twistedTimeKernel_fourier_integrable_from_decay
    (f : ZetaAdmissibleFunction) (σ : ℝ) :
    Integrable
      (fun y : ℝ =>
        zetaCompletedExplicitFormulaPhi f (σ + 2 * π * (-y) * I))
      (volume : Measure ℝ) := by
  rcases zetaPhi_verticalStripRapidDecay_of_admissible_owner f σ σ 4 with
    ⟨C, hCpos, hCbound⟩
  let majorant : ℝ → ℝ :=
    fun y : ℝ => C * (1 + ‖y * (-(2 * π))‖) ^ (-(4 : ℤ))
  have hmajorant :
      Integrable majorant (volume : Measure ℝ) :=
    zetaCompletedExplicitFormula_scaled_fourthOrderMajorant_integrable.const_mul C
  have hmeas :
      AEStronglyMeasurable
        (fun y : ℝ =>
          zetaCompletedExplicitFormulaPhi f (σ + 2 * π * (-y) * I))
        (volume : Measure ℝ) := by
    have hkernel_integrable :
        Integrable
          (fun t : ℝ =>
            Complex.exp ((σ : ℂ) * (t : ℂ)) * f.toZetaTestFunction' t) :=
      zetaCompletedExplicitFormula_twistedTimeKernel_integrable f σ
    have hfourier_continuous :
        Continuous
          (𝓕 (fun t : ℝ =>
            Complex.exp ((σ : ℂ) * (t : ℂ)) * f.toZetaTestFunction' t)) :=
      VectorFourier.fourierIntegral_continuous
        Real.continuous_fourierChar continuous_inner hkernel_integrable
    have hfourier_meas :
        AEStronglyMeasurable
          (𝓕 (fun t : ℝ =>
            Complex.exp ((σ : ℂ) * (t : ℂ)) * f.toZetaTestFunction' t))
          (volume : Measure ℝ) :=
      hfourier_continuous.aestronglyMeasurable
    have heq :
        (fun y : ℝ =>
          zetaCompletedExplicitFormulaPhi f (σ + 2 * π * (-y) * I)) =
        𝓕 (fun t : ℝ =>
          Complex.exp ((σ : ℂ) * (t : ℂ)) * f.toZetaTestFunction' t) := by
      funext y
      exact
        (zetaCompletedExplicitFormula_twistedTimeKernel_fourier_eq_phi_reflected
          f σ y).symm
    exact Eq.subst
      (motive := fun φ : ℝ → ℂ =>
        AEStronglyMeasurable φ (volume : Measure ℝ))
      heq.symm
      hfourier_meas
  have hbound :
      ∀ y : ℝ,
        ‖zetaCompletedExplicitFormulaPhi f (σ + 2 * π * (-y) * I)‖
          ≤ majorant y := by
    intro y
    have hre :
        ((σ : ℂ) + 2 * π * (-y) * I).re = σ :=
      zetaCompletedExplicitFormula_reflectedVerticalLine_re σ y
    have him :
        ((σ : ℂ) + 2 * π * (-y) * I).im = y * (-(2 * π)) :=
      zetaCompletedExplicitFormula_reflectedVerticalLine_im σ y
    have hleft :
        σ ≤ ((σ : ℂ) + 2 * π * (-y) * I).re :=
      le_of_eq hre.symm
    have hright :
        ((σ : ℂ) + 2 * π * (-y) * I).re ≤ σ :=
      le_of_eq hre
    have hdecay :
        ‖zetaCompletedExplicitFormulaPhi f
            ((σ : ℂ) + 2 * π * (-y) * I)‖
          ≤ C *
            (1 + ‖((σ : ℂ) + 2 * π * (-y) * I).im‖) ^ (-(4 : ℤ)) :=
      hCbound ((σ : ℂ) + 2 * π * (-y) * I) hleft hright
    exact
      le_trans hdecay
        (le_of_eq
          (congrArg (fun u : ℝ => C * (1 + ‖u‖) ^ (-(4 : ℤ))) him))
  exact
    explicitFormulaAffineKernel_integrable_of_pointwise_integrable_majorant
      (fun y : ℝ =>
        zetaCompletedExplicitFormulaPhi f (σ + 2 * π * (-y) * I))
      majorant hmajorant hmeas hbound

/-- The Fourier transform of the horizontally twisted time kernel is
integrable.

This is the Paley-Wiener decay consequence needed by Fourier inversion. -/
theorem zetaCompletedExplicitFormula_twistedTimeKernel_fourier_integrable
    (f : ZetaAdmissibleFunction) (σ : ℝ) :
    Integrable
      (𝓕 (fun t : ℝ =>
        Complex.exp ((σ : ℂ) * (t : ℂ)) * f.toZetaTestFunction' t)) := by
  have hline :
      Integrable
        (fun y : ℝ =>
          zetaCompletedExplicitFormulaPhi f (σ + 2 * π * (-y) * I))
        (volume : Measure ℝ) :=
    zetaCompletedExplicitFormula_twistedTimeKernel_fourier_integrable_from_decay
      f σ
  have heq :
      𝓕 (fun t : ℝ =>
          Complex.exp ((σ : ℂ) * (t : ℂ)) * f.toZetaTestFunction' t) =
        fun y : ℝ =>
          zetaCompletedExplicitFormulaPhi f (σ + 2 * π * (-y) * I) := by
    funext y
    exact
      zetaCompletedExplicitFormula_twistedTimeKernel_fourier_eq_phi_reflected
        f σ y
  exact Eq.subst
    (motive := fun φ : ℝ → ℂ =>
      Integrable φ (volume : Measure ℝ))
    heq.symm
    hline

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
