import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaZeroKreinGram.WeilCriterion.OwnerParts.CompletedAffineInverseGammaTransport
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaZeroKreinGram.WeilCriterion.OwnerParts.AutocorrelationAnalyticPackage
import Mathlib.Topology.Basic

/-!
# Completed affine inverse-Gamma shift

The regular coupled inverse-Gamma packet is transported before its
archimedean and elementary correction summands are separated.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open MeasureTheory
open scoped Topology

namespace ZetaAdmissibleFunction

/-- The integral of the difference kernel is the difference of its two
integrals. -/
theorem zetaCompletedAffineInverseGammaRightReflectedDifferenceKernel_integral_eq_sub_of_integrable
    (probe : ZetaAdmissibleFunction)
    (family : ExplicitFormulaContourFamily)
    (rightIntegrable :
      Integrable
        (zetaCompletedExplicitFormulaInverseGammaRightAffineKernel
          probe family)
        (volume : Measure ℝ))
    (leftIntegrable :
      Integrable
        (zetaCompletedExplicitFormulaPrimeLeftReflectedInverseGammaKernel
          probe family)
        (volume : Measure ℝ)) :
    (∫ t : ℝ,
      zetaCompletedAffineInverseGammaRightReflectedDifferenceKernel
        probe family t) =
      (∫ t : ℝ,
        zetaCompletedExplicitFormulaInverseGammaRightAffineKernel
          probe family t) -
        ∫ t : ℝ,
          zetaCompletedExplicitFormulaPrimeLeftReflectedInverseGammaKernel
            probe family t :=
  integral_sub rightIntegrable leftIntegrable

/-- The integral of the difference kernel is the difference of its two
integrals. -/
theorem zetaCompletedAffineInverseGammaRightReflectedDifferenceKernel_integral_eq_sub
    (probe : ZetaAdmissibleFunction)
    (family : ExplicitFormulaContourFamily)
    (analyticPackage :
      ExplicitFormulaFamilyAnalyticPackage probe family) :
    (∫ t : ℝ,
      zetaCompletedAffineInverseGammaRightReflectedDifferenceKernel
        probe family t) =
      (∫ t : ℝ,
        zetaCompletedExplicitFormulaInverseGammaRightAffineKernel
          probe family t) -
        ∫ t : ℝ,
          zetaCompletedExplicitFormulaPrimeLeftReflectedInverseGammaKernel
            probe family t :=
  zetaCompletedAffineInverseGammaRightReflectedDifferenceKernel_integral_eq_sub_of_integrable
    probe
    family
    (zetaCompletedExplicitFormulaInverseGammaRightAffineKernel_integrable
      probe family analyticPackage)
    (zetaCompletedExplicitFormulaPrimeLeftReflectedInverseGammaKernel_integrable_direct_shiftOwner
      probe family analyticPackage)

/-- The whole-line regular affine inverse-Gamma packet has exactly the
Hermitian archimedean critical-line value. -/
theorem zetaCompletedAffineInverseGammaRightReflectedDifferenceKernel_integral_eq_hermitian_owner
    (f : ZetaAdmissibleFunction)
    (hPhi : ZetaPhiAnalyticControl (convolutionAutocorrelation f))
    (hLog : CompletedZetaNegLogDerivControl (convolutionAutocorrelation f)) :
    let probe : ZetaAdmissibleFunction := convolutionAutocorrelation f
    let family : ExplicitFormulaContourFamily :=
      zetaCompletedExplicitFormula_autocorrelation_contourFamily f
    (∫ t : ℝ,
      zetaCompletedAffineInverseGammaRightReflectedDifferenceKernel
        probe family t) =
      zetaCompletedExplicitFormulaHermitianArchimedeanContribution probe :=
  let probe : ZetaAdmissibleFunction := convolutionAutocorrelation f
  let family : ExplicitFormulaContourFamily :=
    zetaCompletedExplicitFormula_autocorrelation_contourFamily f
  let transportValue :
      (∫ t : ℝ,
        zetaCompletedAffineInverseGammaRightReflectedDifferenceKernel
          probe family t) =
        ∫ t : ℝ,
          zetaCompletedHermitianInverseGammaIntegrand probe t :=
    zetaCompletedAffineInverseGamma_integral_eq_hermitianInverseGamma_owner
      f hPhi hLog
  let criticalLineValue :
      (∫ t : ℝ,
        zetaCompletedHermitianInverseGammaIntegrand probe t) =
        zetaCompletedExplicitFormulaHermitianArchimedeanContribution probe :=
    zetaCompletedHermitianInverseGammaIntegrand_integral_eq_archimedeanContribution
      probe
  Eq.trans transportValue criticalLineValue

/-- Scheduled finite windows of the regular affine inverse-Gamma packet
converge to its Hermitian archimedean value. -/
theorem zetaCompletedAffineInverseGammaRightReflectedDifferenceKernel_scheduledWindow_tendsto_hermitian_owner
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
          zetaCompletedAffineInverseGammaRightReflectedDifferenceKernel
            probe family t)
      Filter.atTop
      (𝓝
        (zetaCompletedExplicitFormulaHermitianArchimedeanContribution
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
            zetaCompletedAffineInverseGammaRightReflectedDifferenceKernel
              probe family t)
        Filter.atTop
        (𝓝
          (∫ t : ℝ,
            zetaCompletedAffineInverseGammaRightReflectedDifferenceKernel
              probe family t)) :=
    explicitFormulaScheduledRectangleWindowIntegral_tendsto_integral
      family
      analyticPackage.height_schedule.height
      (zetaCompletedAffineInverseGammaRightReflectedDifferenceKernel
        probe family)
      analyticPackage.height_schedule.cofinal
      (zetaCompletedAffineInverseGammaRightReflectedDifferenceKernel_integrable
        probe family analyticPackage)
  let valueEquality :
      (∫ t : ℝ,
        zetaCompletedAffineInverseGammaRightReflectedDifferenceKernel
          probe family t) =
        zetaCompletedExplicitFormulaHermitianArchimedeanContribution probe :=
    zetaCompletedAffineInverseGammaRightReflectedDifferenceKernel_integral_eq_hermitian_owner
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
            zetaCompletedAffineInverseGammaRightReflectedDifferenceKernel
              probe family t)
        Filter.atTop
        (𝓝 value))
    valueEquality
    integralLimit

/-- The affine inverse-Gamma packet is the Hermitian archimedean value. -/
theorem zetaCompletedAffineInverseGammaRightReflectedDifferenceKernel_integral_eq_archimedean_owner
    (f : ZetaAdmissibleFunction)
    (hPhi : ZetaPhiAnalyticControl (convolutionAutocorrelation f))
    (hLog : CompletedZetaNegLogDerivControl (convolutionAutocorrelation f)) :
    let probe : ZetaAdmissibleFunction := convolutionAutocorrelation f
    let family : ExplicitFormulaContourFamily :=
      zetaCompletedExplicitFormula_autocorrelation_contourFamily f
    (∫ t : ℝ,
      zetaCompletedAffineInverseGammaRightReflectedDifferenceKernel
        probe family t) =
      zetaCompletedExplicitFormulaHermitianArchimedeanContribution probe :=
  zetaCompletedAffineInverseGammaRightReflectedDifferenceKernel_integral_eq_hermitian_owner
    f hPhi hLog

end ZetaAdmissibleFunction

end

end LFunctions
end Boundary
