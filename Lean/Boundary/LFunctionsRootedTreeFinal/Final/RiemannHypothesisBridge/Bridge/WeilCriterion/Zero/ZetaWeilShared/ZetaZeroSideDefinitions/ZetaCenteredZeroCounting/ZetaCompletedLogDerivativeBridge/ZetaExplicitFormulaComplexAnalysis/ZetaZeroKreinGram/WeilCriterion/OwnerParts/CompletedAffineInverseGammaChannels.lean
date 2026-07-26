import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.InverseGammaAffineKernelEstimate
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.PrimeLeftReflectedTermKernelAlgebra
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.ArchimedeanGammaBinetMajorants
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.ArchimedeanGammaBinetTransport
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaCompletedHilbertSource.ZetaHermitianPacket.ArchimedeanCriticalLineIntegrability

/-!
# Completed affine inverse-Gamma channels

Coupled right/reflected-right channel definitions, pointwise algebra, and
coherence-free integrability.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open MeasureTheory

namespace ZetaAdmissibleFunction
/-- The coupled right/reflected-right inverse-Gamma kernel. -/
noncomputable def zetaCompletedAffineInverseGammaRightReflectedDifferenceKernel
    (probe : ZetaAdmissibleFunction)
    (family : ExplicitFormulaContourFamily)
    (t : ℝ) : ℂ :=
  zetaCompletedExplicitFormulaInverseGammaRightAffineKernel
      probe family t -
    zetaCompletedExplicitFormulaPrimeLeftReflectedInverseGammaKernel
      probe family t

/-- The coupled inverse-Gamma kernel unfolds as right minus reflected right. -/
theorem zetaCompletedAffineInverseGammaRightReflectedDifferenceKernel_eq
    (probe : ZetaAdmissibleFunction)
    (family : ExplicitFormulaContourFamily)
    (t : ℝ) :
    zetaCompletedAffineInverseGammaRightReflectedDifferenceKernel
        probe family t =
      zetaCompletedExplicitFormulaInverseGammaRightAffineKernel
          probe family t -
        zetaCompletedExplicitFormulaPrimeLeftReflectedInverseGammaKernel
          probe family t :=
  rfl

/-- The coupled right/reflected-right archimedean channel. -/
noncomputable def zetaCompletedAffineArchimedeanRightReflectedDifferenceKernel
    (probe : ZetaAdmissibleFunction)
    (family : ExplicitFormulaContourFamily)
    (t : ℝ) : ℂ :=
  zetaCompletedExplicitFormulaArchimedeanRightAffineKernel
      probe family t -
    zetaCompletedExplicitFormulaPrimeLeftReflectedArchimedeanKernel
      probe family t

/-- The coupled right/reflected-right elementary correction channel. -/
noncomputable def zetaCompletedAffineCorrectionRightReflectedDifferenceKernel
    (probe : ZetaAdmissibleFunction)
    (family : ExplicitFormulaContourFamily)
    (t : ℝ) : ℂ :=
  zetaCompletedExplicitFormulaCorrectionRightAffineKernel
      probe family t -
    zetaCompletedExplicitFormulaPrimeLeftReflectedCorrectionKernel
      probe family t

/-- The right affine inverse-Gamma kernel splits pointwise into its
archimedean and elementary correction channels. -/
theorem zetaCompletedExplicitFormulaInverseGammaRightAffineKernel_eq_archimedean_add_correction_shiftOwner
    (probe : ZetaAdmissibleFunction)
    (family : ExplicitFormulaContourFamily)
    (t : ℝ) :
    zetaCompletedExplicitFormulaInverseGammaRightAffineKernel
        probe family t =
      zetaCompletedExplicitFormulaArchimedeanRightAffineKernel
          probe family t +
        zetaCompletedExplicitFormulaCorrectionRightAffineKernel
          probe family t :=
  let spectralPoint : ℂ :=
    zetaCompletedExplicitFormulaRightAffineLine family t
  let transformValue : ℂ :=
    zetaCompletedExplicitFormulaPhi probe
      (zetaCompletedExplicitFormulaRightCenteredAffineLine family t)
  let logarithmicDerivativeEquality :
      inverseGammaCompletionLogDeriv spectralPoint =
        explicitFormulaArchimedeanLogDerivative spectralPoint +
          explicitFormulaCorrectionLogDerivative spectralPoint :=
    let archimedeanEquality :
        explicitFormulaArchimedeanLogDerivative spectralPoint =
          inverseGammaCompletionLogDeriv spectralPoint -
            explicitFormulaCorrectionLogDerivative spectralPoint :=
      rfl
    Eq.trans
      (sub_add_cancel
        (inverseGammaCompletionLogDeriv spectralPoint)
        (explicitFormulaCorrectionLogDerivative spectralPoint)).symm
      (congrArg
        (fun value : ℂ =>
          value + explicitFormulaCorrectionLogDerivative spectralPoint)
        archimedeanEquality.symm)
  let unfoldLeft :
      zetaCompletedExplicitFormulaInverseGammaRightAffineKernel
        probe family t =
        inverseGammaCompletionLogDeriv spectralPoint * transformValue :=
    rfl
  let derivativeTransport :
      inverseGammaCompletionLogDeriv spectralPoint * transformValue =
        (explicitFormulaArchimedeanLogDerivative spectralPoint +
          explicitFormulaCorrectionLogDerivative spectralPoint) *
            transformValue :=
    congrArg (fun value : ℂ => value * transformValue)
        logarithmicDerivativeEquality
  let distribute :
      (explicitFormulaArchimedeanLogDerivative spectralPoint +
          explicitFormulaCorrectionLogDerivative spectralPoint) *
            transformValue =
        explicitFormulaArchimedeanLogDerivative spectralPoint *
          transformValue +
          explicitFormulaCorrectionLogDerivative spectralPoint *
            transformValue :=
    add_mul
        (explicitFormulaArchimedeanLogDerivative spectralPoint)
        (explicitFormulaCorrectionLogDerivative spectralPoint)
        transformValue
  let foldRight :
      explicitFormulaArchimedeanLogDerivative spectralPoint *
          transformValue +
          explicitFormulaCorrectionLogDerivative spectralPoint *
            transformValue =
        zetaCompletedExplicitFormulaArchimedeanRightAffineKernel
          probe family t +
        zetaCompletedExplicitFormulaCorrectionRightAffineKernel
          probe family t :=
    rfl
  Eq.trans unfoldLeft
    (Eq.trans derivativeTransport
      (Eq.trans distribute foldRight))

/-- The coupled inverse-Gamma kernel is the sum of the coupled archimedean
and elementary correction channels. -/
theorem zetaCompletedAffineInverseGammaRightReflectedDifferenceKernel_eq_archimedean_add_correction
    (probe : ZetaAdmissibleFunction)
    (family : ExplicitFormulaContourFamily)
    (t : ℝ) :
    zetaCompletedAffineInverseGammaRightReflectedDifferenceKernel
        probe family t =
      zetaCompletedAffineArchimedeanRightReflectedDifferenceKernel
          probe family t +
        zetaCompletedAffineCorrectionRightReflectedDifferenceKernel
          probe family t :=
  let rightArchimedean : ℂ :=
    zetaCompletedExplicitFormulaArchimedeanRightAffineKernel
      probe family t
  let rightCorrection : ℂ :=
    zetaCompletedExplicitFormulaCorrectionRightAffineKernel
      probe family t
  let reflectedArchimedean : ℂ :=
    zetaCompletedExplicitFormulaPrimeLeftReflectedArchimedeanKernel
      probe family t
  let reflectedCorrection : ℂ :=
    zetaCompletedExplicitFormulaPrimeLeftReflectedCorrectionKernel
      probe family t
  let rightEquality :
      zetaCompletedExplicitFormulaInverseGammaRightAffineKernel
          probe family t =
        rightArchimedean + rightCorrection :=
    zetaCompletedExplicitFormulaInverseGammaRightAffineKernel_eq_archimedean_add_correction_shiftOwner
      probe family t
  let reflectedEquality :
      zetaCompletedExplicitFormulaPrimeLeftReflectedInverseGammaKernel
          probe family t =
        reflectedArchimedean + reflectedCorrection :=
    (zetaCompletedExplicitFormulaPrimeLeftReflectedArchimedeanKernel_add_correction_eq_inverseGamma
      probe family t).symm
  let splitTotal :
      zetaCompletedAffineInverseGammaRightReflectedDifferenceKernel
        probe family t =
        (rightArchimedean + rightCorrection) -
          (reflectedArchimedean + reflectedCorrection) :=
    congrArg₂ HSub.hSub rightEquality reflectedEquality
  let regroup :
      (rightArchimedean + rightCorrection) -
          (reflectedArchimedean + reflectedCorrection) =
        (rightArchimedean - reflectedArchimedean) +
          (rightCorrection - reflectedCorrection) :=
    add_sub_add_comm
        rightArchimedean rightCorrection
        reflectedArchimedean reflectedCorrection
  let foldRight :
      (rightArchimedean - reflectedArchimedean) +
          (rightCorrection - reflectedCorrection) =
        zetaCompletedAffineArchimedeanRightReflectedDifferenceKernel
          probe family t +
        zetaCompletedAffineCorrectionRightReflectedDifferenceKernel
          probe family t :=
    rfl
  Eq.trans splitTotal
    (Eq.trans regroup foldRight)

/-- Direct integrability of the reflected inverse-Gamma kernel. -/
theorem zetaCompletedExplicitFormulaPrimeLeftReflectedInverseGammaKernel_integrable_direct_shiftOwner
    (probe : ZetaAdmissibleFunction)
    (family : ExplicitFormulaContourFamily)
    (analyticPackage :
      ExplicitFormulaFamilyAnalyticPackage probe family) :
    Integrable
      (zetaCompletedExplicitFormulaPrimeLeftReflectedInverseGammaKernel
        probe family)
      (volume : Measure ℝ) :=
  match
    zetaCompletedExplicitFormulaInverseGammaCompletionLogDeriv_rightAffineLine_bound_of_gammaBinet_owner
      family with
  | ⟨bound, boundNonnegative, factorBound⟩ =>
      zetaCompletedExplicitFormulaPrimeLeftReflectedInverseGammaKernel_integrable_of_right_factor_bound
        probe family analyticPackage bound boundNonnegative factorBound

/-- Direct integrability of the coupled right/reflected-right inverse-Gamma
packet. -/
theorem zetaCompletedAffineInverseGammaRightReflectedDifferenceKernel_integrable
    (probe : ZetaAdmissibleFunction)
    (family : ExplicitFormulaContourFamily)
    (analyticPackage :
      ExplicitFormulaFamilyAnalyticPackage probe family) :
    Integrable
      (zetaCompletedAffineInverseGammaRightReflectedDifferenceKernel
        probe family)
      (volume : Measure ℝ) :=
  let rightIntegrable :
      Integrable
        (zetaCompletedExplicitFormulaInverseGammaRightAffineKernel
          probe family)
        (volume : Measure ℝ) :=
    zetaCompletedExplicitFormulaInverseGammaRightAffineKernel_integrable
      probe family analyticPackage
  let reflectedIntegrable :
      Integrable
        (zetaCompletedExplicitFormulaPrimeLeftReflectedInverseGammaKernel
          probe family)
        (volume : Measure ℝ) :=
    zetaCompletedExplicitFormulaPrimeLeftReflectedInverseGammaKernel_integrable_direct_shiftOwner
      probe family analyticPackage
  rightIntegrable.sub reflectedIntegrable

/-- Coherence-free integrability of the reflected elementary correction
channel. -/
theorem zetaCompletedExplicitFormulaPrimeLeftReflectedCorrectionKernel_integrable_shiftOwner
    (probe : ZetaAdmissibleFunction)
    (family : ExplicitFormulaContourFamily)
    (analyticPackage :
      ExplicitFormulaFamilyAnalyticPackage probe family) :
    Integrable
      (zetaCompletedExplicitFormulaPrimeLeftReflectedCorrectionKernel
        probe family)
      (volume : Measure ℝ) :=
  let bound : ℝ :=
    (1 : ℝ) / family.c + (1 : ℝ) / (family.c - 1)
  let boundNonnegative : 0 ≤ bound :=
    add_nonneg
      (div_nonneg zero_le_one family.c_pos.le)
      (div_nonneg zero_le_one (sub_pos.mpr family.c_gt_one).le)
  let reflectedMeasurable :
      AEStronglyMeasurable
        (fun t : ℝ =>
          -(explicitFormulaCorrectionLogDerivative
            (zetaCompletedExplicitFormulaRightAffineLine family (-t))))
        (volume : Measure ℝ) :=
    let lineMeasurable :
        Measurable
          (fun t : ℝ =>
            zetaCompletedExplicitFormulaRightAffineLine family (-t)) :=
      measurable_const.add
        ((Complex.measurable_ofReal.comp measurable_neg).mul measurable_const)
    let correctionMeasurable :
        Measurable
          (fun t : ℝ =>
            explicitFormulaCorrectionLogDerivative
              (zetaCompletedExplicitFormulaRightAffineLine family (-t))) :=
      let line : ℝ → ℂ := fun t : ℝ =>
        zetaCompletedExplicitFormulaRightAffineLine family (-t)
      let zeroPoleMeasurable :
          Measurable (fun t : ℝ => (-1 : ℂ) / line t) :=
        measurable_const.div lineMeasurable
      let onePoleMeasurable :
          Measurable (fun t : ℝ => (1 : ℂ) / (line t - 1)) :=
        measurable_const.div (lineMeasurable.sub measurable_const)
      let correctionEquality :
          (fun t : ℝ =>
            explicitFormulaCorrectionLogDerivative (line t)) =
            fun t : ℝ =>
              (-1 : ℂ) / line t - (1 : ℂ) / (line t - 1) :=
        funext
          (fun t : ℝ =>
            explicitFormulaCorrectionLogDerivative_eq_poleCorrection
              (line t))
      Eq.subst
        (motive := fun function : ℝ → ℂ => Measurable function)
        correctionEquality.symm
        (zeroPoleMeasurable.sub onePoleMeasurable)
    correctionMeasurable.neg.aestronglyMeasurable
  zetaCompletedExplicitFormulaPrimeLeftReflectedCorrectionKernel_integrable_of_right_factor_bound
    probe family analyticPackage bound boundNonnegative reflectedMeasurable
    (zetaCompletedExplicitFormulaCorrectionLogDerivative_rightAffineLine_linear_bound
      family)

/-- Coherence-free integrability of the coupled correction channel. -/
theorem zetaCompletedAffineCorrectionRightReflectedDifferenceKernel_integrable
    (probe : ZetaAdmissibleFunction)
    (family : ExplicitFormulaContourFamily)
    (analyticPackage :
      ExplicitFormulaFamilyAnalyticPackage probe family) :
    Integrable
      (zetaCompletedAffineCorrectionRightReflectedDifferenceKernel
        probe family)
      (volume : Measure ℝ) :=
  let rightIntegrable : Integrable
      (zetaCompletedExplicitFormulaCorrectionRightAffineKernel probe family)
        (volume : Measure ℝ) :=
    zetaCompletedExplicitFormulaCorrectionRightAffineKernel_integrable_ownerGammaBinetLineValue
      probe family analyticPackage
  let reflectedIntegrable : Integrable
      (zetaCompletedExplicitFormulaPrimeLeftReflectedCorrectionKernel probe family)
        (volume : Measure ℝ) :=
    zetaCompletedExplicitFormulaPrimeLeftReflectedCorrectionKernel_integrable_shiftOwner
      probe family analyticPackage
  rightIntegrable.sub reflectedIntegrable

/-- Coupled archimedean integrability by correction-channel subtraction. -/
theorem zetaCompletedAffineArchimedeanRightReflectedDifferenceKernel_integrable
    (probe : ZetaAdmissibleFunction)
    (family : ExplicitFormulaContourFamily)
    (analyticPackage :
      ExplicitFormulaFamilyAnalyticPackage probe family) :
    Integrable
      (zetaCompletedAffineArchimedeanRightReflectedDifferenceKernel
        probe family)
      (volume : Measure ℝ) :=
  let rightIntegrable : Integrable
      (zetaCompletedExplicitFormulaInverseGammaRightAffineKernel probe family)
        (volume : Measure ℝ) :=
    zetaCompletedExplicitFormulaInverseGammaRightAffineKernel_integrable
      probe family analyticPackage
  let reflectedIntegrable : Integrable
      (zetaCompletedExplicitFormulaPrimeLeftReflectedInverseGammaKernel probe family)
        (volume : Measure ℝ) :=
    zetaCompletedExplicitFormulaPrimeLeftReflectedInverseGammaKernel_integrable_direct_shiftOwner
      probe family analyticPackage
  let totalIntegrable :
      Integrable
        (zetaCompletedAffineInverseGammaRightReflectedDifferenceKernel
          probe family)
        (volume : Measure ℝ) :=
    rightIntegrable.sub reflectedIntegrable
  let correctionIntegrable :
      Integrable
        (zetaCompletedAffineCorrectionRightReflectedDifferenceKernel
          probe family)
        (volume : Measure ℝ) :=
    zetaCompletedAffineCorrectionRightReflectedDifferenceKernel_integrable
      probe family analyticPackage
  let differenceIntegrable :
      Integrable
        (fun t : ℝ =>
          zetaCompletedAffineInverseGammaRightReflectedDifferenceKernel
              probe family t -
            zetaCompletedAffineCorrectionRightReflectedDifferenceKernel
              probe family t)
        (volume : Measure ℝ) :=
    totalIntegrable.sub correctionIntegrable
  let functionEquality :
      (fun t : ℝ =>
        zetaCompletedAffineInverseGammaRightReflectedDifferenceKernel
            probe family t -
          zetaCompletedAffineCorrectionRightReflectedDifferenceKernel
            probe family t) =
        zetaCompletedAffineArchimedeanRightReflectedDifferenceKernel
          probe family :=
    funext
      (fun t : ℝ =>
        Eq.trans
          (congrArg
            (fun value : ℂ =>
              value -
                zetaCompletedAffineCorrectionRightReflectedDifferenceKernel
                  probe family t)
            (zetaCompletedAffineInverseGammaRightReflectedDifferenceKernel_eq_archimedean_add_correction
              probe family t))
          (add_sub_cancel_right
            (zetaCompletedAffineArchimedeanRightReflectedDifferenceKernel
              probe family t)
            (zetaCompletedAffineCorrectionRightReflectedDifferenceKernel
              probe family t)))
  Eq.subst
    (motive := fun function : ℝ → ℂ =>
      Integrable function (volume : Measure ℝ))
    functionEquality
    differenceIntegrable


end ZetaAdmissibleFunction

end

end LFunctions
end Boundary
