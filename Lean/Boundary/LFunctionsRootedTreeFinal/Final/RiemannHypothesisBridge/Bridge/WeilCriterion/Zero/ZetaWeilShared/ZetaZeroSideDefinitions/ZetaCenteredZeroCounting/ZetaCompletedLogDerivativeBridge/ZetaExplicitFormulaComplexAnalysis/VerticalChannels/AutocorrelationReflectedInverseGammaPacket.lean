import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.VerticalChannels.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaZeroKreinGram.WeilCriterion.OwnerParts.CompletedAffineArchimedeanAnySchedule

/-!
# Autocorrelation reflected inverse-Gamma packet

This file connects the vertical-channel autocorrelation package to the
reflected affine inverse-Gamma archimedean packet used by the physical
autocorrelation lane.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open MeasureTheory

namespace ZetaAdmissibleFunction

/-- The reflected affine archimedean/correction packet converges to the
Hermitian archimedean boundary contribution along any supplied autocorrelation
schedule. -/
theorem zetaCompletedExplicitFormula_autocorrelation_reflectedInverseGammaPacket_tendsto_hermitianArchimedean
    (f : ZetaAdmissibleFunction)
    (schedule :
      ExplicitFormulaHorizontalAvoidingHeightSchedule
        (zetaCompletedExplicitFormula_autocorrelation_contourFamily f))
    (hPhi : ZetaPhiAnalyticControl (convolutionAutocorrelation f))
    (hLog : CompletedZetaNegLogDerivControl (convolutionAutocorrelation f)) :
    let probe : ZetaAdmissibleFunction := convolutionAutocorrelation f
    let family : ExplicitFormulaContourFamily :=
      zetaCompletedExplicitFormula_autocorrelation_contourFamily f
    let analyticPackage :
        ExplicitFormulaFamilyAnalyticPackage probe family :=
      zetaCompletedExplicitFormula_autocorrelation_familyAnalyticPackage
        f schedule hPhi hLog
    Tendsto
      (fun u : ℝ =>
        (∫ t in Set.Icc
            (-(family.rectangle
              (analyticPackage.height_schedule.height u)).T)
            (family.rectangle
              (analyticPackage.height_schedule.height u)).T,
          zetaCompletedAffineArchimedeanRightReflectedDifferenceKernel
            probe family t) +
          ∫ t in Set.Icc
            (-(family.rectangle
              (analyticPackage.height_schedule.height u)).T)
            (family.rectangle
              (analyticPackage.height_schedule.height u)).T,
            zetaCompletedAffineCorrectionRightReflectedDifferenceKernel
              probe family t)
      atTop
      (𝓝
        (zetaCompletedExplicitFormulaHermitianArchimedeanContribution
          probe)) :=
  let probe : ZetaAdmissibleFunction := convolutionAutocorrelation f
  let family : ExplicitFormulaContourFamily :=
    zetaCompletedExplicitFormula_autocorrelation_contourFamily f
  let analyticPackage :
      ExplicitFormulaFamilyAnalyticPackage probe family :=
    zetaCompletedExplicitFormula_autocorrelation_familyAnalyticPackage
      f schedule hPhi hLog
  let harch :
      Tendsto
        (fun u : ℝ =>
          ∫ t in Set.Icc
              (-(family.rectangle
                (analyticPackage.height_schedule.height u)).T)
              (family.rectangle
                (analyticPackage.height_schedule.height u)).T,
            zetaCompletedAffineArchimedeanRightReflectedDifferenceKernel
              probe family t)
        atTop
        (𝓝
          (zetaCompletedExplicitFormulaHermitianArchimedeanContribution probe -
            zetaCompletedExplicitFormulaCorrectionStandardContourContribution
              probe)) :=
    zetaCompletedAffineArchimedeanRightReflectedDifferenceKernel_scheduledWindow_tendsto_hermitian_sub_correction_of_schedule
      f schedule hPhi hLog
  let hcorr :
      Tendsto
        (fun u : ℝ =>
          ∫ t in Set.Icc
              (-(family.rectangle
                (analyticPackage.height_schedule.height u)).T)
              (family.rectangle
                (analyticPackage.height_schedule.height u)).T,
            zetaCompletedAffineCorrectionRightReflectedDifferenceKernel
              probe family t)
        atTop
        (𝓝
          (zetaCompletedExplicitFormulaCorrectionStandardContourContribution
            probe)) :=
    zetaCompletedAffineCorrectionRightReflectedDifferenceKernel_scheduledWindow_tendsto_standard_of_schedule
      f schedule hPhi hLog
  let hsum :
      Tendsto
        (fun u : ℝ =>
          (∫ t in Set.Icc
              (-(family.rectangle
                (analyticPackage.height_schedule.height u)).T)
              (family.rectangle
                (analyticPackage.height_schedule.height u)).T,
            zetaCompletedAffineArchimedeanRightReflectedDifferenceKernel
              probe family t) +
            ∫ t in Set.Icc
              (-(family.rectangle
                (analyticPackage.height_schedule.height u)).T)
              (family.rectangle
                (analyticPackage.height_schedule.height u)).T,
              zetaCompletedAffineCorrectionRightReflectedDifferenceKernel
                probe family t)
        atTop
        (𝓝
          ((zetaCompletedExplicitFormulaHermitianArchimedeanContribution probe -
              zetaCompletedExplicitFormulaCorrectionStandardContourContribution
                probe) +
            zetaCompletedExplicitFormulaCorrectionStandardContourContribution
              probe)) :=
    harch.add hcorr
  let htarget :
      (zetaCompletedExplicitFormulaHermitianArchimedeanContribution probe -
          zetaCompletedExplicitFormulaCorrectionStandardContourContribution
            probe) +
        zetaCompletedExplicitFormulaCorrectionStandardContourContribution
          probe =
        zetaCompletedExplicitFormulaHermitianArchimedeanContribution probe :=
    sub_add_cancel
      (zetaCompletedExplicitFormulaHermitianArchimedeanContribution probe)
      (zetaCompletedExplicitFormulaCorrectionStandardContourContribution
        probe)
  Eq.subst
    (motive := fun value : ℂ =>
      Tendsto
        (fun u : ℝ =>
          (∫ t in Set.Icc
              (-(family.rectangle
                (analyticPackage.height_schedule.height u)).T)
              (family.rectangle
                (analyticPackage.height_schedule.height u)).T,
            zetaCompletedAffineArchimedeanRightReflectedDifferenceKernel
              probe family t) +
            ∫ t in Set.Icc
              (-(family.rectangle
                (analyticPackage.height_schedule.height u)).T)
              (family.rectangle
                (analyticPackage.height_schedule.height u)).T,
              zetaCompletedAffineCorrectionRightReflectedDifferenceKernel
                probe family t)
        atTop
        (𝓝 value))
    htarget
    hsum

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
