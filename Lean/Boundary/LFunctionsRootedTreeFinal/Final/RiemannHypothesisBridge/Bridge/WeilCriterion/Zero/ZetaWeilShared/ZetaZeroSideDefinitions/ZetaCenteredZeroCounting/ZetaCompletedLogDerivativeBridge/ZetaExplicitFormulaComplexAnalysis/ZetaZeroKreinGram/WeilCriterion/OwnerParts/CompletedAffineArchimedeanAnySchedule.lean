import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaZeroKreinGram.WeilCriterion.OwnerParts.CompletedAffineArchimedeanValue

/-!
# Completed affine archimedean value on supplied schedules

The reflected affine archimedean packet has already been identified with the
Hermitian archimedean value minus the standard correction.  This file only
transports that whole-line value along an arbitrary supplied height schedule.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open MeasureTheory

namespace ZetaAdmissibleFunction

/-- The coupled right/reflected archimedean packet converges along any supplied
autocorrelation schedule. -/
theorem zetaCompletedAffineArchimedeanRightReflectedDifferenceKernel_scheduledWindow_tendsto_hermitian_sub_correction_of_schedule
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
  let probe : ZetaAdmissibleFunction := convolutionAutocorrelation f
  let family : ExplicitFormulaContourFamily :=
    zetaCompletedExplicitFormula_autocorrelation_contourFamily f
  let analyticPackage :
      ExplicitFormulaFamilyAnalyticPackage probe family :=
    zetaCompletedExplicitFormula_autocorrelation_familyAnalyticPackage
      f schedule hPhi hLog
  let integralLimit :
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
        (𝓝 value))
    valueEquality
    integralLimit

/-- The coupled right/reflected correction packet converges along any supplied
autocorrelation schedule. -/
theorem zetaCompletedAffineCorrectionRightReflectedDifferenceKernel_scheduledWindow_tendsto_standard_of_schedule
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
  let probe : ZetaAdmissibleFunction := convolutionAutocorrelation f
  let family : ExplicitFormulaContourFamily :=
    zetaCompletedExplicitFormula_autocorrelation_contourFamily f
  let analyticPackage :
      ExplicitFormulaFamilyAnalyticPackage probe family :=
    zetaCompletedExplicitFormula_autocorrelation_familyAnalyticPackage
      f schedule hPhi hLog
  let integralLimit :
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
          (∫ t : ℝ,
            zetaCompletedAffineCorrectionRightReflectedDifferenceKernel
              probe family t)) :=
    explicitFormulaScheduledRectangleWindowIntegral_tendsto_integral
      family
      analyticPackage.height_schedule.height
      (zetaCompletedAffineCorrectionRightReflectedDifferenceKernel
        probe family)
      analyticPackage.height_schedule.cofinal
      (zetaCompletedAffineCorrectionRightReflectedDifferenceKernel_integrable
        probe family analyticPackage)
  let valueEquality :
      (∫ t : ℝ,
        zetaCompletedAffineCorrectionRightReflectedDifferenceKernel
          probe family t) =
        zetaCompletedExplicitFormulaCorrectionStandardContourContribution
          probe :=
    zetaCompletedAffineCorrectionRightReflectedDifferenceKernel_integral_eq_standard_owner
      f hPhi hLog
  Eq.subst
    (motive := fun value : ℂ =>
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
        (𝓝 value))
    valueEquality
    integralLimit

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
