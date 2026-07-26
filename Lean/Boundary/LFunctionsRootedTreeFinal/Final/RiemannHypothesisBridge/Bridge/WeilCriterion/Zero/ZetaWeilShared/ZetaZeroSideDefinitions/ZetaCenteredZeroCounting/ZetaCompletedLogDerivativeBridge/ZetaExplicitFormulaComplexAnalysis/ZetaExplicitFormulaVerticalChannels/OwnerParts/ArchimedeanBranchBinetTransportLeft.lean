import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.ArchimedeanBranchBinetTransport

/-!
# Left branch Binet archimedean transport leaves

This file keeps the left full-line branch wrapper separate so each owner part
stays small.
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

/-- Branch-coherence form of the scheduled left affine theorem from full-line
Binet main and remainder values. -/
theorem zetaCompletedExplicitFormulaArchimedeanLeftAffineKernel_scheduledWindow_tendsto_neg_phiZero_of_fullLineBinetValues_branch
    (f : ZetaAdmissibleFunction)
    (F : ExplicitFormulaVerticallyRegularContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F.toContourFamily)
    (hbranch : Complex.binetBranchLogGammaCoherence)
    (hmain_value :
      (∫ t : ℝ,
        zetaCompletedExplicitFormulaArchimedeanLeftBinetMainKernel
          f F.toContourFamily t) =
        -(zetaCompletedExplicitFormulaPhi f 0))
    (hremainder_value :
      (∫ t : ℝ,
        zetaCompletedExplicitFormulaArchimedeanLeftBinetRemainderKernel
          f F.toContourFamily t) =
        0) :
    Tendsto
      (fun u : ℝ =>
        ∫ t in Set.Icc
            (-(F.toContourFamily.rectangle
                (h.height_schedule.height u)).T)
            (F.toContourFamily.rectangle
                (h.height_schedule.height u)).T,
          zetaCompletedExplicitFormulaArchimedeanLeftAffineKernel
            f F.toContourFamily t)
      atTop
      (𝓝 (-(zetaCompletedExplicitFormulaPhi f 0))) :=
  let hregular :
      zetaCompletedExplicitFormulaLeftAffineLineGammaRegular
        F.toContourFamily :=
    zetaCompletedExplicitFormulaLeftAffineLineGammaRegular_of_verticallyRegular
      F
  let hmain_integrable :
      ∀ u : ℝ,
        Integrable
          (zetaCompletedExplicitFormulaArchimedeanLeftBinetMainKernel
            f F.toContourFamily)
          (volume.restrict
            (Set.Icc
              (-(F.toContourFamily.rectangle
                  (h.height_schedule.height u)).T)
              (F.toContourFamily.rectangle
                  (h.height_schedule.height u)).T)) :=
    fun u =>
      zetaCompletedExplicitFormulaArchimedeanLeftBinetMainKernel_integrable_restrict_Icc
        f F.toContourFamily h hregular
        (-(F.toContourFamily.rectangle (h.height_schedule.height u)).T)
        (F.toContourFamily.rectangle (h.height_schedule.height u)).T
  let hremainder_integrable :
      ∀ u : ℝ,
        Integrable
          (zetaCompletedExplicitFormulaArchimedeanLeftBinetRemainderKernel
            f F.toContourFamily)
          (volume.restrict
            (Set.Icc
              (-(F.toContourFamily.rectangle
                  (h.height_schedule.height u)).T)
              (F.toContourFamily.rectangle
                  (h.height_schedule.height u)).T)) :=
    fun u =>
      zetaCompletedExplicitFormulaArchimedeanLeftBinetRemainderKernel_integrable_restrict_Icc
        f F.toContourFamily h hregular
        (-(F.toContourFamily.rectangle (h.height_schedule.height u)).T)
        (F.toContourFamily.rectangle (h.height_schedule.height u)).T
  let hmain_integral :
      Tendsto
        (fun u : ℝ =>
          ∫ t in Set.Icc
              (-(F.toContourFamily.rectangle
                  (h.height_schedule.height u)).T)
              (F.toContourFamily.rectangle
                  (h.height_schedule.height u)).T,
            zetaCompletedExplicitFormulaArchimedeanLeftBinetMainKernel
              f F.toContourFamily t)
        atTop
        (𝓝 (∫ t : ℝ,
          zetaCompletedExplicitFormulaArchimedeanLeftBinetMainKernel
            f F.toContourFamily t)) :=
    zetaCompletedExplicitFormulaArchimedeanLeftBinetMainKernel_scheduledWindow_tendsto_integral
      f F h hregular
  let hmain :
      Tendsto
        (fun u : ℝ =>
          ∫ t in Set.Icc
              (-(F.toContourFamily.rectangle
                  (h.height_schedule.height u)).T)
              (F.toContourFamily.rectangle
                  (h.height_schedule.height u)).T,
            zetaCompletedExplicitFormulaArchimedeanLeftBinetMainKernel
              f F.toContourFamily t)
        atTop
        (𝓝 (-(zetaCompletedExplicitFormulaPhi f 0))) :=
    Eq.subst
      (motive := fun z : ℂ =>
        Tendsto
          (fun u : ℝ =>
            ∫ t in Set.Icc
                (-(F.toContourFamily.rectangle
                    (h.height_schedule.height u)).T)
                (F.toContourFamily.rectangle
                    (h.height_schedule.height u)).T,
              zetaCompletedExplicitFormulaArchimedeanLeftBinetMainKernel
                f F.toContourFamily t)
          atTop
          (𝓝 z))
      hmain_value
      hmain_integral
  let hremainder_integral :
      Tendsto
        (fun u : ℝ =>
          ∫ t in Set.Icc
              (-(F.toContourFamily.rectangle
                  (h.height_schedule.height u)).T)
              (F.toContourFamily.rectangle
                  (h.height_schedule.height u)).T,
            zetaCompletedExplicitFormulaArchimedeanLeftBinetRemainderKernel
              f F.toContourFamily t)
        atTop
        (𝓝 (∫ t : ℝ,
          zetaCompletedExplicitFormulaArchimedeanLeftBinetRemainderKernel
            f F.toContourFamily t)) :=
    zetaCompletedExplicitFormulaArchimedeanLeftBinetRemainderKernel_scheduledWindow_tendsto_integral
      f F h hregular
  let hremainder :
      Tendsto
        (fun u : ℝ =>
          ∫ t in Set.Icc
              (-(F.toContourFamily.rectangle
                  (h.height_schedule.height u)).T)
              (F.toContourFamily.rectangle
                  (h.height_schedule.height u)).T,
            zetaCompletedExplicitFormulaArchimedeanLeftBinetRemainderKernel
              f F.toContourFamily t)
        atTop
        (𝓝 0) :=
    Eq.subst
      (motive := fun z : ℂ =>
        Tendsto
          (fun u : ℝ =>
            ∫ t in Set.Icc
                (-(F.toContourFamily.rectangle
                    (h.height_schedule.height u)).T)
                (F.toContourFamily.rectangle
                    (h.height_schedule.height u)).T,
              zetaCompletedExplicitFormulaArchimedeanLeftBinetRemainderKernel
                f F.toContourFamily t)
          atTop
          (𝓝 z))
      hremainder_value
      hremainder_integral
  zetaCompletedExplicitFormulaArchimedeanLeftAffineKernel_scheduledWindow_tendsto_neg_phiZero_of_binetMain_remainder_branch
    f F h hbranch hmain_integrable hremainder_integrable hmain hremainder

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
