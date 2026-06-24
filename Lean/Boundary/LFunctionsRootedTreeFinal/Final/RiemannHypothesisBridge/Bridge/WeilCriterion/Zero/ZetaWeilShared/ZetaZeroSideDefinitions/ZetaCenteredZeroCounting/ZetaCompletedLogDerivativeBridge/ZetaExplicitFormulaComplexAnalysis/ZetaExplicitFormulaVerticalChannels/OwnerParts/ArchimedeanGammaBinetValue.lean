import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.ArchimedeanGammaBinetLineValue

/-!
# Archimedean Gamma/Binet value

This file owns the genuine Gamma/Binet scheduled value theorem for the
archimedean right-minus-left affine kernel.  It is intentionally separate from
inverse-Gamma recombination: inverse-Gamma difference values contain both the
archimedean component and the elementary correction component.

The two individual line values live in
`ArchimedeanGammaBinetLineValue.lean`; this file only assembles the
right-minus-left normalization.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open Complex
open Filter
open LSeries ArithmeticFunction
open MeasureTheory
open scoped ArithmeticFunction
open scoped Topology

namespace ZetaAdmissibleFunction

/-- Scheduled Gamma/Binet value of the right archimedean affine line.

This file is a downstream wrapper: the scheduled coupled transform value is
owned in `ArchimedeanGammaBinetLineCore`, and the line-value file transports
it to the affine line. -/
theorem zetaCompletedExplicitFormulaArchimedeanRightAffineKernel_scheduledWindow_tendsto_phiZero_ownerGammaBinetValue
    (f : ZetaAdmissibleFunction)
    (F : ExplicitFormulaVerticallyRegularContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F.toContourFamily)
    (hcoh : Complex.gammaBinetPrincipalLogCoherence) :
    Tendsto
      (fun u : ℝ =>
        ∫ t in Set.Icc
            (-(F.toContourFamily.rectangle (h.height_schedule.height u)).T)
            (F.toContourFamily.rectangle (h.height_schedule.height u)).T,
          zetaCompletedExplicitFormulaArchimedeanRightAffineKernel
            f F.toContourFamily t)
      atTop
      (𝓝 (zetaCompletedExplicitFormulaPhi f 0)) := by
  exact
    zetaCompletedExplicitFormulaArchimedeanRightAffineKernel_scheduledWindow_tendsto_phiZero_ownerGammaBinetLineValue
      f F h hcoh

/-- Scheduled Gamma/Binet value of the left archimedean affine line.

This is the shifted-left analogue of the right wrapper above; the analytic
leaf remains the scheduled coupled transform theorem in the line core. -/
theorem zetaCompletedExplicitFormulaArchimedeanLeftAffineKernel_scheduledWindow_tendsto_neg_phiZero_ownerGammaBinetValue
    (f : ZetaAdmissibleFunction)
    (F : ExplicitFormulaVerticallyRegularContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F.toContourFamily)
    (hcoh : Complex.gammaBinetPrincipalLogCoherence) :
    Tendsto
      (fun u : ℝ =>
        ∫ t in Set.Icc
            (-(F.toContourFamily.rectangle (h.height_schedule.height u)).T)
            (F.toContourFamily.rectangle (h.height_schedule.height u)).T,
          zetaCompletedExplicitFormulaArchimedeanLeftAffineKernel
            f F.toContourFamily t)
      atTop
      (𝓝 (-(zetaCompletedExplicitFormulaPhi f 0))) := by
  exact
    zetaCompletedExplicitFormulaArchimedeanLeftAffineKernel_scheduledWindow_tendsto_neg_phiZero_ownerGammaBinetLineValue
      f F h hcoh

/-- Finite-window right-minus-left decomposition of the archimedean affine
kernel. -/
theorem zetaCompletedExplicitFormulaArchimedeanDifferenceAffineKernel_intervalIntegral_eq_right_sub_left
    (f : ZetaAdmissibleFunction)
    (F : ExplicitFormulaVerticallyRegularContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F.toContourFamily)
    (hcoh : Complex.gammaBinetPrincipalLogCoherence)
    (T : ℝ) :
    (∫ t in Set.Icc (-T) T,
      zetaCompletedExplicitFormulaArchimedeanDifferenceAffineKernel
        f F.toContourFamily t) =
      (∫ t in Set.Icc (-T) T,
        zetaCompletedExplicitFormulaArchimedeanRightAffineKernel
          f F.toContourFamily t) -
        ∫ t in Set.Icc (-T) T,
          zetaCompletedExplicitFormulaArchimedeanLeftAffineKernel
            f F.toContourFamily t := by
  have hright_integrable :
      Integrable
        (zetaCompletedExplicitFormulaArchimedeanRightAffineKernel
          f F.toContourFamily)
        (volume : Measure ℝ) := by
    have hinv :
        Integrable
          (zetaCompletedExplicitFormulaInverseGammaRightAffineKernel
            f F.toContourFamily)
          (volume : Measure ℝ) :=
      zetaCompletedExplicitFormulaInverseGammaRightAffineKernel_integrable
        f F.toContourFamily h hcoh
    have hzero :
        Integrable
          (zetaCompletedExplicitFormulaCorrectionRightZeroPoleAffineKernel
            f F.toContourFamily)
          (volume : Measure ℝ) :=
      zetaCompletedExplicitFormulaCorrectionRightZeroPoleAffineKernel_integrable_ownerBounds
        f F.toContourFamily h
    have hone :
        Integrable
          (zetaCompletedExplicitFormulaCorrectionRightOnePoleAffineKernel
            f F.toContourFamily)
          (volume : Measure ℝ) :=
      zetaCompletedExplicitFormulaCorrectionRightOnePoleAffineKernel_integrable_ownerBounds
        f F.toContourFamily h
    have hcorrection_sum :
        Integrable
          (fun t : ℝ =>
            zetaCompletedExplicitFormulaCorrectionRightZeroPoleAffineKernel
              f F.toContourFamily t +
              zetaCompletedExplicitFormulaCorrectionRightOnePoleAffineKernel
                f F.toContourFamily t)
          (volume : Measure ℝ) :=
      hzero.add hone
    have hcorrection :
        Integrable
          (zetaCompletedExplicitFormulaCorrectionRightAffineKernel
            f F.toContourFamily)
          (volume : Measure ℝ) :=
      hcorrection_sum.congr
        (Filter.Eventually.of_forall
          (fun t =>
            (zetaCompletedExplicitFormulaCorrectionRightAffineKernel_eq_zeroPole_add_onePole
              f F.toContourFamily t).symm))
    have hdiff :
        Integrable
          (fun t : ℝ =>
            zetaCompletedExplicitFormulaInverseGammaRightAffineKernel
              f F.toContourFamily t -
              zetaCompletedExplicitFormulaCorrectionRightAffineKernel
                f F.toContourFamily t)
          (volume : Measure ℝ) :=
      hinv.sub hcorrection
    have hpoint :
        (zetaCompletedExplicitFormulaArchimedeanRightAffineKernel
          f F.toContourFamily) =ᵐ[volume]
          fun t : ℝ =>
            zetaCompletedExplicitFormulaInverseGammaRightAffineKernel
              f F.toContourFamily t -
              zetaCompletedExplicitFormulaCorrectionRightAffineKernel
                f F.toContourFamily t :=
      Filter.Eventually.of_forall
        (fun t =>
          Eq.trans
            (add_sub_cancel
              (zetaCompletedExplicitFormulaArchimedeanRightAffineKernel
                f F.toContourFamily t)
              (zetaCompletedExplicitFormulaCorrectionRightAffineKernel
                f F.toContourFamily t)).symm
            (congrArg
              (fun z : ℂ =>
                z - zetaCompletedExplicitFormulaCorrectionRightAffineKernel
                  f F.toContourFamily t)
              (zetaCompletedExplicitFormulaArchimedeanRightAffineKernel_add_correction_eq_inverseGamma
                f F.toContourFamily t)))
    exact hdiff.congr hpoint.symm
  have hleft_integrable :
      Integrable
        (zetaCompletedExplicitFormulaArchimedeanLeftAffineKernel
          f F.toContourFamily)
        (volume : Measure ℝ) := by
    have hregular :
        zetaCompletedExplicitFormulaLeftAffineLineGammaRegular
          F.toContourFamily :=
      zetaCompletedExplicitFormulaLeftAffineLineGammaRegular_of_verticallyRegular
        F
    have hinv :
        Integrable
          (zetaCompletedExplicitFormulaInverseGammaLeftAffineKernel
            f F.toContourFamily)
          (volume : Measure ℝ) :=
      zetaCompletedExplicitFormulaInverseGammaLeftAffineKernel_integrable
        f F.toContourFamily h hregular hcoh
    have hzero :
        Integrable
          (zetaCompletedExplicitFormulaCorrectionLeftZeroPoleAffineKernel
            f F.toContourFamily)
          (volume : Measure ℝ) :=
      zetaCompletedExplicitFormulaCorrectionLeftZeroPoleAffineKernel_integrable_ownerBounds
        f F.toContourFamily h
    have hone :
        Integrable
          (zetaCompletedExplicitFormulaCorrectionLeftOnePoleAffineKernel
            f F.toContourFamily)
          (volume : Measure ℝ) :=
      zetaCompletedExplicitFormulaCorrectionLeftOnePoleAffineKernel_integrable_ownerBounds
        f F.toContourFamily h
    have hcorrection_sum :
        Integrable
          (fun t : ℝ =>
            zetaCompletedExplicitFormulaCorrectionLeftZeroPoleAffineKernel
              f F.toContourFamily t +
              zetaCompletedExplicitFormulaCorrectionLeftOnePoleAffineKernel
                f F.toContourFamily t)
          (volume : Measure ℝ) :=
      hzero.add hone
    have hcorrection :
        Integrable
          (zetaCompletedExplicitFormulaCorrectionLeftAffineKernel
            f F.toContourFamily)
          (volume : Measure ℝ) :=
      hcorrection_sum.congr
        (Filter.Eventually.of_forall
          (fun t =>
            (zetaCompletedExplicitFormulaCorrectionLeftAffineKernel_eq_zeroPole_add_onePole
              f F.toContourFamily t).symm))
    have hdiff :
        Integrable
          (fun t : ℝ =>
            zetaCompletedExplicitFormulaInverseGammaLeftAffineKernel
              f F.toContourFamily t -
              zetaCompletedExplicitFormulaCorrectionLeftAffineKernel
                f F.toContourFamily t)
          (volume : Measure ℝ) :=
      hinv.sub hcorrection
    have hpoint :
        (zetaCompletedExplicitFormulaArchimedeanLeftAffineKernel
          f F.toContourFamily) =ᵐ[volume]
          fun t : ℝ =>
            zetaCompletedExplicitFormulaInverseGammaLeftAffineKernel
              f F.toContourFamily t -
              zetaCompletedExplicitFormulaCorrectionLeftAffineKernel
                f F.toContourFamily t :=
      Filter.Eventually.of_forall
        (fun t =>
          Eq.trans
            (add_sub_cancel
              (zetaCompletedExplicitFormulaArchimedeanLeftAffineKernel
                f F.toContourFamily t)
              (zetaCompletedExplicitFormulaCorrectionLeftAffineKernel
                f F.toContourFamily t)).symm
            (congrArg
              (fun z : ℂ =>
                z - zetaCompletedExplicitFormulaCorrectionLeftAffineKernel
                  f F.toContourFamily t)
              (zetaCompletedExplicitFormulaArchimedeanLeftAffineKernel_add_correction_eq_inverseGamma
                f F.toContourFamily t)))
    exact hdiff.congr hpoint.symm
  have hsub :
      (∫ t in Set.Icc (-T) T,
          zetaCompletedExplicitFormulaArchimedeanRightAffineKernel
            f F.toContourFamily t) -
        ∫ t in Set.Icc (-T) T,
          zetaCompletedExplicitFormulaArchimedeanLeftAffineKernel
            f F.toContourFamily t =
        ∫ t in Set.Icc (-T) T,
          zetaCompletedExplicitFormulaArchimedeanRightAffineKernel
            f F.toContourFamily t -
            zetaCompletedExplicitFormulaArchimedeanLeftAffineKernel
              f F.toContourFamily t :=
    explicitFormulaSymmetricIntervalIntegral_sub_eq_integral_sub
      (zetaCompletedExplicitFormulaArchimedeanRightAffineKernel
        f F.toContourFamily)
      (zetaCompletedExplicitFormulaArchimedeanLeftAffineKernel
        f F.toContourFamily)
      hright_integrable hleft_integrable T
  have hpoint :
      (fun t : ℝ =>
        zetaCompletedExplicitFormulaArchimedeanDifferenceAffineKernel
          f F.toContourFamily t) =
      fun t : ℝ =>
        zetaCompletedExplicitFormulaArchimedeanRightAffineKernel
          f F.toContourFamily t -
          zetaCompletedExplicitFormulaArchimedeanLeftAffineKernel
            f F.toContourFamily t := by
    rfl
  calc
    (∫ t in Set.Icc (-T) T,
      zetaCompletedExplicitFormulaArchimedeanDifferenceAffineKernel
        f F.toContourFamily t) =
        ∫ t in Set.Icc (-T) T,
          zetaCompletedExplicitFormulaArchimedeanRightAffineKernel
            f F.toContourFamily t -
            zetaCompletedExplicitFormulaArchimedeanLeftAffineKernel
              f F.toContourFamily t := by
      exact congrArg
        (fun φ : ℝ → ℂ => ∫ t in Set.Icc (-T) T, φ t)
        hpoint
    _ =
        (∫ t in Set.Icc (-T) T,
          zetaCompletedExplicitFormulaArchimedeanRightAffineKernel
            f F.toContourFamily t) -
          ∫ t in Set.Icc (-T) T,
            zetaCompletedExplicitFormulaArchimedeanLeftAffineKernel
              f F.toContourFamily t := by
      exact hsub.symm

/-- Algebraic assembly of the scheduled archimedean value from the separate
right and left Gamma/Binet line values. -/
theorem zetaCompletedExplicitFormulaArchimedeanDifferenceAffineKernel_scheduledWindow_tendsto_archimedeanContribution_of_right_left
    (f : ZetaAdmissibleFunction)
    (F : ExplicitFormulaVerticallyRegularContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F.toContourFamily)
    (hcoh : Complex.gammaBinetPrincipalLogCoherence)
    (hright :
      Tendsto
        (fun u : ℝ =>
          ∫ t in Set.Icc
              (-(F.toContourFamily.rectangle (h.height_schedule.height u)).T)
              (F.toContourFamily.rectangle (h.height_schedule.height u)).T,
            zetaCompletedExplicitFormulaArchimedeanRightAffineKernel
              f F.toContourFamily t)
        atTop
        (𝓝 (zetaCompletedExplicitFormulaPhi f 0)))
    (hleft :
      Tendsto
        (fun u : ℝ =>
          ∫ t in Set.Icc
              (-(F.toContourFamily.rectangle (h.height_schedule.height u)).T)
              (F.toContourFamily.rectangle (h.height_schedule.height u)).T,
            zetaCompletedExplicitFormulaArchimedeanLeftAffineKernel
              f F.toContourFamily t)
        atTop
        (𝓝 (-(zetaCompletedExplicitFormulaPhi f 0)))) :
    Tendsto
      (fun u : ℝ =>
        ∫ t in Set.Icc
            (-(F.toContourFamily.rectangle (h.height_schedule.height u)).T)
            (F.toContourFamily.rectangle (h.height_schedule.height u)).T,
          zetaCompletedExplicitFormulaArchimedeanDifferenceAffineKernel
            f F.toContourFamily t)
      atTop
      (𝓝 (zetaCompletedExplicitFormulaArchimedeanContribution f)) := by
  let rightWindow : ℝ → ℂ := fun u : ℝ =>
    ∫ t in Set.Icc
        (-(F.toContourFamily.rectangle (h.height_schedule.height u)).T)
        (F.toContourFamily.rectangle (h.height_schedule.height u)).T,
      zetaCompletedExplicitFormulaArchimedeanRightAffineKernel
        f F.toContourFamily t
  let leftWindow : ℝ → ℂ := fun u : ℝ =>
    ∫ t in Set.Icc
        (-(F.toContourFamily.rectangle (h.height_schedule.height u)).T)
        (F.toContourFamily.rectangle (h.height_schedule.height u)).T,
      zetaCompletedExplicitFormulaArchimedeanLeftAffineKernel
        f F.toContourFamily t
  let differenceWindow : ℝ → ℂ := fun u : ℝ =>
    ∫ t in Set.Icc
        (-(F.toContourFamily.rectangle (h.height_schedule.height u)).T)
        (F.toContourFamily.rectangle (h.height_schedule.height u)).T,
      zetaCompletedExplicitFormulaArchimedeanDifferenceAffineKernel
        f F.toContourFamily t
  have hsub_limit :
      Tendsto (fun u : ℝ => rightWindow u - leftWindow u) atTop
        (𝓝 (zetaCompletedExplicitFormulaPhi f 0 -
          (-(zetaCompletedExplicitFormulaPhi f 0)))) :=
    hright.sub hleft
  have htarget :
      zetaCompletedExplicitFormulaPhi f 0 -
          (-(zetaCompletedExplicitFormulaPhi f 0)) =
        zetaCompletedExplicitFormulaArchimedeanContribution f := by
    calc
      zetaCompletedExplicitFormulaPhi f 0 -
          (-(zetaCompletedExplicitFormulaPhi f 0)) =
          zetaCompletedExplicitFormulaPhi f 0 +
            zetaCompletedExplicitFormulaPhi f 0 := by
        exact Eq.trans
          (sub_eq_add_neg
            (zetaCompletedExplicitFormulaPhi f 0)
            (-(zetaCompletedExplicitFormulaPhi f 0)))
          (congrArg
            (fun z : ℂ => zetaCompletedExplicitFormulaPhi f 0 + z)
            (neg_neg (zetaCompletedExplicitFormulaPhi f 0)))
      _ = (2 : ℂ) * zetaCompletedExplicitFormulaPhi f 0 := by
        exact (two_mul (zetaCompletedExplicitFormulaPhi f 0)).symm
      _ = zetaCompletedExplicitFormulaArchimedeanContribution f := by
        exact (zetaCompletedExplicitFormulaArchimedeanContribution_eq f).symm
  have hsub_target :
      Tendsto (fun u : ℝ => rightWindow u - leftWindow u) atTop
        (𝓝 (zetaCompletedExplicitFormulaArchimedeanContribution f)) := by
    exact Eq.subst
      (motive := fun z : ℂ =>
        Tendsto (fun u : ℝ => rightWindow u - leftWindow u) atTop (𝓝 z))
      htarget
      hsub_limit
  have hpoint :
      differenceWindow = fun u : ℝ => rightWindow u - leftWindow u := by
    funext u
    exact
      zetaCompletedExplicitFormulaArchimedeanDifferenceAffineKernel_intervalIntegral_eq_right_sub_left
        f F h hcoh (h.height_schedule.height u)
  exact Eq.subst
    (motive := fun φ : ℝ → ℂ =>
      Tendsto φ atTop
        (𝓝 (zetaCompletedExplicitFormulaArchimedeanContribution f)))
    hpoint.symm
    hsub_target

/-- Owner analytic leaf: scheduled-window value theorem for the archimedean
right-minus-left affine kernel.

Proof target:

1. Prove the paired right/left Gamma/Binet vertical-line decompositions for
   `archLogDeriv`.
2. Use `Complex.gammaBinetPrincipalLogCoherence` only for branch coherence in
   that special-function decomposition.
3. Control the Binet remainder by the existing Paley-Wiener vertical decay of
   `Phi_f`.
4. Track the right-minus-left sign and identify the resulting boundary term
   with `zetaCompletedExplicitFormulaArchimedeanContribution f`.

This theorem must not be proved from the inverse-Gamma component normalization,
because that normalization consumes the archimedean component value. -/
theorem zetaCompletedExplicitFormulaArchimedeanDifferenceAffineKernel_scheduledWindow_tendsto_archimedeanContribution_ownerGammaBinetValue
    (f : ZetaAdmissibleFunction)
    (F : ExplicitFormulaVerticallyRegularContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F.toContourFamily)
    (hcoh : Complex.gammaBinetPrincipalLogCoherence) :
    Tendsto
      (fun u : ℝ =>
        ∫ t in Set.Icc
            (-(F.toContourFamily.rectangle (h.height_schedule.height u)).T)
            (F.toContourFamily.rectangle (h.height_schedule.height u)).T,
          zetaCompletedExplicitFormulaArchimedeanDifferenceAffineKernel
            f F.toContourFamily t)
      atTop
      (𝓝 (zetaCompletedExplicitFormulaArchimedeanContribution f)) := by
  exact
    zetaCompletedExplicitFormulaArchimedeanDifferenceAffineKernel_scheduledWindow_tendsto_archimedeanContribution_of_right_left
      f F h hcoh
      (zetaCompletedExplicitFormulaArchimedeanRightAffineKernel_scheduledWindow_tendsto_phiZero_ownerGammaBinetValue
        f F h hcoh)
      (zetaCompletedExplicitFormulaArchimedeanLeftAffineKernel_scheduledWindow_tendsto_neg_phiZero_ownerGammaBinetValue
        f F h hcoh)

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
