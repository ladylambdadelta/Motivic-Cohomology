import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaZeroKreinGram.WeilCriterion.OwnerParts.CompletedAffineRegularContourTransport
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaZeroKreinGram.WeilCriterion.OwnerParts.AutocorrelationAnalyticPackage
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaZeroKreinGram.WeilCriterion.OwnerParts.CompletedAffineArchimedeanSeedTransport
import Mathlib.Topology.Basic

/-!
# Completed affine archimedean value

The coupled affine Gamma-factor functional is identified with the Hermitian
centered archimedean Weil functional.  Scheduled convergence is then ordinary
integrable-window exhaustion.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open MeasureTheory
open scoped Topology

namespace ZetaAdmissibleFunction

/-- The explicit paired finite-Binet transform evaluates to the Hermitian
archimedean value after removal of the crossed correction residue. -/
theorem zetaCompletedAffineArchimedeanPairedBinetKernel_integral_eq_hermitian_sub_correction_owner
    (f : ZetaAdmissibleFunction)
    (hPhi : ZetaPhiAnalyticControl (convolutionAutocorrelation f))
    (hLog : CompletedZetaNegLogDerivControl (convolutionAutocorrelation f)) :
    let probe : ZetaAdmissibleFunction := convolutionAutocorrelation f
    let family : ExplicitFormulaContourFamily :=
      zetaCompletedExplicitFormula_autocorrelation_contourFamily f
    (∫ t : ℝ,
      zetaCompletedAffineArchimedeanPairedBinetKernel
        probe family t) =
      zetaCompletedExplicitFormulaHermitianArchimedeanContribution probe -
        zetaCompletedExplicitFormulaCorrectionStandardContourContribution
          probe :=
  let probe : ZetaAdmissibleFunction := convolutionAutocorrelation f
  let family : ExplicitFormulaContourFamily :=
    zetaCompletedExplicitFormula_autocorrelation_contourFamily f
  let inverseGammaPacket : ℝ → ℂ :=
    zetaCompletedAffineInverseGammaRightReflectedDifferenceKernel
      probe family
  let archimedeanPacket : ℝ → ℂ :=
    zetaCompletedAffineArchimedeanRightReflectedDifferenceKernel
      probe family
  let correctionPacket : ℝ → ℂ :=
    zetaCompletedAffineCorrectionRightReflectedDifferenceKernel
      probe family
  let pairedFunctionEquality :
      zetaCompletedAffineArchimedeanPairedBinetKernel
          probe family =
        zetaCompletedAffineArchimedeanSeedPairedBinetKernel
          f family :=
    funext
      (fun t : ℝ =>
        zetaCompletedAffineArchimedeanPairedBinetKernel_convolutionAutocorrelation_eq_seed
          f family t)
  let pairedIntegralEquality :
      (∫ t : ℝ,
        zetaCompletedAffineArchimedeanPairedBinetKernel
          probe family t) =
        ∫ t : ℝ,
          zetaCompletedAffineArchimedeanSeedPairedBinetKernel
            f family t :=
    congrArg
      (fun integrand : ℝ → ℂ => ∫ t : ℝ, integrand t)
      pairedFunctionEquality
  let archimedeanPairedEquality :
      archimedeanPacket =
        zetaCompletedAffineArchimedeanPairedBinetKernel probe family :=
    funext
      (fun t : ℝ =>
        zetaCompletedAffineArchimedeanRightReflectedDifferenceKernel_eq_pairedBinet_shiftOwner
          probe family t)
  let inverseGammaFunctionEquality :
      inverseGammaPacket =
        fun t : ℝ => archimedeanPacket t + correctionPacket t :=
    funext
      (fun t : ℝ =>
        zetaCompletedAffineInverseGammaRightReflectedDifferenceKernel_eq_archimedean_add_correction
          probe family t)
  let analyticPackage :
      ExplicitFormulaFamilyAnalyticPackage probe family :=
    CleanAutocorrelationAnalyticPackage.zetaCompletedExplicitFormula_autocorrelation_familyAnalyticPackage
      f
      (zetaCompletedExplicitFormulaAutocorrelationHorizontalAvoidingSchedule f)
      hPhi
      hLog
  let archimedeanIntegrable :
      Integrable archimedeanPacket (volume : Measure ℝ) :=
    zetaCompletedAffineArchimedeanRightReflectedDifferenceKernel_integrable
      probe family analyticPackage
  let correctionIntegrable :
      Integrable correctionPacket (volume : Measure ℝ) :=
    zetaCompletedAffineCorrectionRightReflectedDifferenceKernel_integrable
      probe family analyticPackage
  let inverseGammaIntegralSplit :
      (∫ t : ℝ, inverseGammaPacket t) =
        (∫ t : ℝ, archimedeanPacket t) +
          ∫ t : ℝ, correctionPacket t :=
    Eq.trans
      (congrArg
        (fun integrand : ℝ → ℂ => ∫ t : ℝ, integrand t)
        inverseGammaFunctionEquality)
      (integral_add archimedeanIntegrable correctionIntegrable)
  let inverseGammaTransport :
      (∫ t : ℝ, inverseGammaPacket t) =
        ∫ t : ℝ,
          zetaCompletedHermitianInverseGammaIntegrand probe t :=
    zetaCompletedAffineRegularInverseGamma_integral_eq_critical_owner f
      hPhi hLog
  let criticalValue :
      (∫ t : ℝ,
        zetaCompletedHermitianInverseGammaIntegrand probe t) =
        zetaCompletedExplicitFormulaHermitianArchimedeanContribution probe :=
    zetaCompletedHermitianInverseGammaIntegrand_integral_eq_archimedeanContribution
      probe
  let correctionValue :
      (∫ t : ℝ, correctionPacket t) =
        zetaCompletedExplicitFormulaCorrectionStandardContourContribution
          probe :=
    zetaCompletedAffineCorrectionRightReflectedDifferenceKernel_integral_eq_standard_owner
      f hPhi hLog
  let packetSumValue :
      (∫ t : ℝ, archimedeanPacket t) +
          ∫ t : ℝ, correctionPacket t =
        zetaCompletedExplicitFormulaHermitianArchimedeanContribution probe :=
    Eq.trans inverseGammaIntegralSplit.symm
      (Eq.trans inverseGammaTransport criticalValue)
  let archimedeanValue :
      (∫ t : ℝ, archimedeanPacket t) =
        zetaCompletedExplicitFormulaHermitianArchimedeanContribution probe -
          zetaCompletedExplicitFormulaCorrectionStandardContourContribution
            probe :=
    (eq_sub_iff_add_eq).mpr
      (Eq.trans
        (congrArg
          (fun value : ℂ =>
            (∫ t : ℝ, archimedeanPacket t) + value)
          correctionValue.symm)
        packetSumValue)
  let pairedIntegralFromArchimedean :
      (∫ t : ℝ,
        zetaCompletedAffineArchimedeanPairedBinetKernel probe family t) =
        ∫ t : ℝ, archimedeanPacket t :=
    congrArg
      (fun integrand : ℝ → ℂ => ∫ t : ℝ, integrand t)
      archimedeanPairedEquality.symm
  Eq.trans pairedIntegralFromArchimedean archimedeanValue

/-- The coupled right/reflected-right affine archimedean functional is the
Hermitian centered value. -/
theorem zetaCompletedAffineArchimedeanRightReflectedDifferenceKernel_integral_eq_hermitian_sub_correction_owner
    (f : ZetaAdmissibleFunction)
    (hPhi : ZetaPhiAnalyticControl (convolutionAutocorrelation f))
    (hLog : CompletedZetaNegLogDerivControl (convolutionAutocorrelation f)) :
    let probe : ZetaAdmissibleFunction := convolutionAutocorrelation f
    let family : ExplicitFormulaContourFamily :=
      zetaCompletedExplicitFormula_autocorrelation_contourFamily f
    (∫ t : ℝ,
      zetaCompletedAffineArchimedeanRightReflectedDifferenceKernel
        probe family t) =
      zetaCompletedExplicitFormulaHermitianArchimedeanContribution probe -
        zetaCompletedExplicitFormulaCorrectionStandardContourContribution
          probe :=
  let probe : ZetaAdmissibleFunction := convolutionAutocorrelation f
  let family : ExplicitFormulaContourFamily :=
    zetaCompletedExplicitFormula_autocorrelation_contourFamily f
  let functionEquality :
      zetaCompletedAffineArchimedeanRightReflectedDifferenceKernel
          probe family =
        zetaCompletedAffineArchimedeanPairedBinetKernel
          probe family :=
    funext
      (fun t : ℝ =>
        zetaCompletedAffineArchimedeanRightReflectedDifferenceKernel_eq_pairedBinet_shiftOwner
          probe family t)
  let integralEquality :
      (∫ t : ℝ,
        zetaCompletedAffineArchimedeanRightReflectedDifferenceKernel
          probe family t) =
        ∫ t : ℝ,
          zetaCompletedAffineArchimedeanPairedBinetKernel
            probe family t :=
    congrArg
      (fun integrand : ℝ → ℂ => ∫ t : ℝ, integrand t)
      functionEquality
  Eq.trans integralEquality
    (zetaCompletedAffineArchimedeanPairedBinetKernel_integral_eq_hermitian_sub_correction_owner
      f hPhi hLog)

/-- Scheduled branch-free value of the coupled archimedean channel. -/
theorem zetaCompletedAffineArchimedeanRightReflectedDifferenceKernel_scheduledWindow_tendsto_hermitian_sub_correction_owner
    (f : ZetaAdmissibleFunction)
    (hPhi : ZetaPhiAnalyticControl (convolutionAutocorrelation f))
    (hLog : CompletedZetaNegLogDerivControl (convolutionAutocorrelation f)) :
    let probe : ZetaAdmissibleFunction := convolutionAutocorrelation f
    let family : ExplicitFormulaContourFamily :=
      zetaCompletedExplicitFormula_autocorrelation_contourFamily f
    let analyticPackage :
        ExplicitFormulaFamilyAnalyticPackage probe family :=
      CleanAutocorrelationAnalyticPackage.zetaCompletedExplicitFormula_autocorrelation_familyAnalyticPackage
        f
        (zetaCompletedExplicitFormulaAutocorrelationHorizontalAvoidingSchedule f)
        hPhi
        hLog
    Filter.Tendsto
      (fun u : ℝ =>
        ∫ t in Set.Icc
            (-(family.rectangle
              (analyticPackage.height_schedule.height u)).T)
            (family.rectangle
              (analyticPackage.height_schedule.height u)).T,
          zetaCompletedAffineArchimedeanRightReflectedDifferenceKernel
            probe family t)
      Filter.atTop
      (𝓝
        (zetaCompletedExplicitFormulaHermitianArchimedeanContribution probe -
          zetaCompletedExplicitFormulaCorrectionStandardContourContribution
            probe)) :=
  let probe : ZetaAdmissibleFunction := convolutionAutocorrelation f
  let family : ExplicitFormulaContourFamily :=
    zetaCompletedExplicitFormula_autocorrelation_contourFamily f
  let analyticPackage :
      ExplicitFormulaFamilyAnalyticPackage probe family :=
    CleanAutocorrelationAnalyticPackage.zetaCompletedExplicitFormula_autocorrelation_familyAnalyticPackage
      f
      (zetaCompletedExplicitFormulaAutocorrelationHorizontalAvoidingSchedule f)
      hPhi
      hLog
  let integralLimit :
      Filter.Tendsto
        (fun u : ℝ =>
          ∫ t in Set.Icc
              (-(family.rectangle
                (analyticPackage.height_schedule.height u)).T)
              (family.rectangle
                (analyticPackage.height_schedule.height u)).T,
            zetaCompletedAffineArchimedeanRightReflectedDifferenceKernel
              probe family t)
        Filter.atTop
        (𝓝
          (∫ t : ℝ,
            zetaCompletedAffineArchimedeanRightReflectedDifferenceKernel
              probe family t)) :=
    explicitFormulaScheduledRectangleWindowIntegral_tendsto_integral
      family
      analyticPackage.height_schedule.height
      (zetaCompletedAffineArchimedeanRightReflectedDifferenceKernel
        probe family)
      analyticPackage.height_schedule.cofinal
      (zetaCompletedAffineArchimedeanRightReflectedDifferenceKernel_integrable
        probe family analyticPackage)
  let valueEquality :
      (∫ t : ℝ,
        zetaCompletedAffineArchimedeanRightReflectedDifferenceKernel
          probe family t) =
        zetaCompletedExplicitFormulaHermitianArchimedeanContribution probe -
          zetaCompletedExplicitFormulaCorrectionStandardContourContribution
            probe :=
    zetaCompletedAffineArchimedeanRightReflectedDifferenceKernel_integral_eq_hermitian_sub_correction_owner
      f hPhi hLog
  Eq.subst
    (motive := fun value : ℂ =>
      Filter.Tendsto
        (fun u : ℝ =>
          ∫ t in Set.Icc
              (-(family.rectangle
                (analyticPackage.height_schedule.height u)).T)
              (family.rectangle
                (analyticPackage.height_schedule.height u)).T,
            zetaCompletedAffineArchimedeanRightReflectedDifferenceKernel
              probe family t)
        Filter.atTop
        (𝓝 value))
    valueEquality
    integralLimit

end ZetaAdmissibleFunction

end

end LFunctions
end Boundary
