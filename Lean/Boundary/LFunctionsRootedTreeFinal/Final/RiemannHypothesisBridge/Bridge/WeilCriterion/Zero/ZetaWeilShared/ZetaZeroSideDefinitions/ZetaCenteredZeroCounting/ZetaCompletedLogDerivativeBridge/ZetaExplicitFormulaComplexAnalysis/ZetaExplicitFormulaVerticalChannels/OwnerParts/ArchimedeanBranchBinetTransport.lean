import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.GammaBinetStirling.BinetBranchCoherence
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.ArchimedeanGammaBinetTransport

/-!
# Branch Binet archimedean transport leaves

This file peels the archimedean affine-kernel leaves that use only the
main-plus-remainder Binet decomposition.  These leaves consume the
branch-correct Binet coherence package instead of the old principal-log
coherence package.
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

/-- Branch-coherence form of right affine main-plus-remainder assembly. -/
theorem zetaCompletedExplicitFormulaArchimedeanRightAffineKernel_scheduledWindow_tendsto_phiZero_of_binetMain_remainder_branch
    (f : ZetaAdmissibleFunction)
    (F : ExplicitFormulaVerticallyRegularContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F.toContourFamily)
    (hbranch : Complex.binetBranchLogGammaCoherence)
    (hmain_integrable :
      ∀ u : ℝ,
        Integrable
          (zetaCompletedExplicitFormulaArchimedeanRightBinetMainKernel
            f F.toContourFamily)
          (volume.restrict
            (Set.Icc
              (-(F.toContourFamily.rectangle
                  (h.height_schedule.height u)).T)
              (F.toContourFamily.rectangle
                  (h.height_schedule.height u)).T)))
    (hremainder_integrable :
      ∀ u : ℝ,
        Integrable
          (zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel
            f F.toContourFamily)
          (volume.restrict
            (Set.Icc
              (-(F.toContourFamily.rectangle
                  (h.height_schedule.height u)).T)
              (F.toContourFamily.rectangle
                  (h.height_schedule.height u)).T)))
    (hmain :
      Tendsto
        (fun u : ℝ =>
          ∫ t in Set.Icc
              (-(F.toContourFamily.rectangle
                  (h.height_schedule.height u)).T)
              (F.toContourFamily.rectangle
                  (h.height_schedule.height u)).T,
            zetaCompletedExplicitFormulaArchimedeanRightBinetMainKernel
              f F.toContourFamily t)
        atTop
        (𝓝 (zetaCompletedExplicitFormulaPhi f 0)))
    (hremainder :
      Tendsto
        (fun u : ℝ =>
          ∫ t in Set.Icc
              (-(F.toContourFamily.rectangle
                  (h.height_schedule.height u)).T)
              (F.toContourFamily.rectangle
                  (h.height_schedule.height u)).T,
            zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel
              f F.toContourFamily t)
        atTop
        (𝓝 0)) :
    Tendsto
      (fun u : ℝ =>
        ∫ t in Set.Icc
            (-(F.toContourFamily.rectangle
                (h.height_schedule.height u)).T)
            (F.toContourFamily.rectangle
                (h.height_schedule.height u)).T,
          zetaCompletedExplicitFormulaArchimedeanRightAffineKernel
            f F.toContourFamily t)
      atTop
      (𝓝 (zetaCompletedExplicitFormulaPhi f 0)) :=
  Eq.subst
    (motive := fun branchData : Complex.binetBranchLogGammaCoherence =>
      Tendsto
        (fun u : ℝ =>
          ∫ t in Set.Icc
              (-(F.toContourFamily.rectangle
                  (h.height_schedule.height u)).T)
              (F.toContourFamily.rectangle
                  (h.height_schedule.height u)).T,
            zetaCompletedExplicitFormulaArchimedeanRightAffineKernel
              f F.toContourFamily t)
        atTop
        (𝓝 (zetaCompletedExplicitFormulaPhi f 0)))
    (Eq.refl hbranch)
    (zetaCompletedExplicitFormula_scheduledWindow_tendsto_of_binetMain_add_remainder
      F.toContourFamily
      h.height_schedule.height
      (zetaCompletedExplicitFormulaArchimedeanRightAffineKernel
        f F.toContourFamily)
      (zetaCompletedExplicitFormulaArchimedeanRightBinetMainKernel
        f F.toContourFamily)
      (zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel
        f F.toContourFamily)
      (zetaCompletedExplicitFormulaPhi f 0)
      (fun t : ℝ =>
        zetaCompletedExplicitFormulaArchimedeanRightAffineKernel_eq_binetMain_add_remainder
          f F.toContourFamily t)
      hmain_integrable
      hremainder_integrable
      hmain
      hremainder)

/-- Branch-coherence form of left affine main-plus-remainder assembly. -/
theorem zetaCompletedExplicitFormulaArchimedeanLeftAffineKernel_scheduledWindow_tendsto_neg_phiZero_of_binetMain_remainder_branch
    (f : ZetaAdmissibleFunction)
    (F : ExplicitFormulaVerticallyRegularContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F.toContourFamily)
    (hbranch : Complex.binetBranchLogGammaCoherence)
    (hmain_integrable :
      ∀ u : ℝ,
        Integrable
          (zetaCompletedExplicitFormulaArchimedeanLeftBinetMainKernel
            f F.toContourFamily)
          (volume.restrict
            (Set.Icc
              (-(F.toContourFamily.rectangle
                  (h.height_schedule.height u)).T)
              (F.toContourFamily.rectangle
                  (h.height_schedule.height u)).T)))
    (hremainder_integrable :
      ∀ u : ℝ,
        Integrable
          (zetaCompletedExplicitFormulaArchimedeanLeftBinetRemainderKernel
            f F.toContourFamily)
          (volume.restrict
            (Set.Icc
              (-(F.toContourFamily.rectangle
                  (h.height_schedule.height u)).T)
              (F.toContourFamily.rectangle
                  (h.height_schedule.height u)).T)))
    (hmain :
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
        (𝓝 (-(zetaCompletedExplicitFormulaPhi f 0))))
    (hremainder :
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
        (𝓝 0)) :
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
  by
    have hregular :
        zetaCompletedExplicitFormulaLeftAffineLineGammaRegular
          F.toContourFamily :=
      zetaCompletedExplicitFormulaLeftAffineLineGammaRegular_of_verticallyRegular
        F
    exact
      zetaCompletedExplicitFormula_scheduledWindow_tendsto_of_binetMain_add_remainder
        F.toContourFamily
        h.height_schedule.height
        (zetaCompletedExplicitFormulaArchimedeanLeftAffineKernel
          f F.toContourFamily)
        (zetaCompletedExplicitFormulaArchimedeanLeftBinetMainKernel
          f F.toContourFamily)
        (zetaCompletedExplicitFormulaArchimedeanLeftBinetRemainderKernel
          f F.toContourFamily)
        (-(zetaCompletedExplicitFormulaPhi f 0))
        (fun t : ℝ =>
          zetaCompletedExplicitFormulaArchimedeanLeftAffineKernel_eq_binetMain_add_remainder
            f F.toContourFamily hregular t)
        hmain_integrable
        hremainder_integrable
        hmain
        hremainder

/-- Branch-coherence form of the scheduled right affine theorem from full-line
Binet main and remainder values. -/
theorem zetaCompletedExplicitFormulaArchimedeanRightAffineKernel_scheduledWindow_tendsto_phiZero_of_fullLineBinetValues_branch
    (f : ZetaAdmissibleFunction)
    (F : ExplicitFormulaVerticallyRegularContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F.toContourFamily)
    (hbranch : Complex.binetBranchLogGammaCoherence)
    (hmain_value :
      (∫ t : ℝ,
        zetaCompletedExplicitFormulaArchimedeanRightBinetMainKernel
          f F.toContourFamily t) =
        zetaCompletedExplicitFormulaPhi f 0)
    (hremainder_value :
      (∫ t : ℝ,
        zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel
          f F.toContourFamily t) =
        0) :
    Tendsto
      (fun u : ℝ =>
        ∫ t in Set.Icc
            (-(F.toContourFamily.rectangle
                (h.height_schedule.height u)).T)
            (F.toContourFamily.rectangle
                (h.height_schedule.height u)).T,
          zetaCompletedExplicitFormulaArchimedeanRightAffineKernel
            f F.toContourFamily t)
      atTop
      (𝓝 (zetaCompletedExplicitFormulaPhi f 0)) :=
  let hmain_integrable :
      ∀ u : ℝ,
        Integrable
          (zetaCompletedExplicitFormulaArchimedeanRightBinetMainKernel
            f F.toContourFamily)
          (volume.restrict
            (Set.Icc
              (-(F.toContourFamily.rectangle
                  (h.height_schedule.height u)).T)
              (F.toContourFamily.rectangle
                  (h.height_schedule.height u)).T)) :=
    fun u =>
      zetaCompletedExplicitFormulaArchimedeanRightBinetMainKernel_integrable_restrict_Icc
        f F.toContourFamily h
        (-(F.toContourFamily.rectangle (h.height_schedule.height u)).T)
        (F.toContourFamily.rectangle (h.height_schedule.height u)).T
  let hremainder_integrable :
      ∀ u : ℝ,
        Integrable
          (zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel
            f F.toContourFamily)
          (volume.restrict
            (Set.Icc
              (-(F.toContourFamily.rectangle
                  (h.height_schedule.height u)).T)
              (F.toContourFamily.rectangle
                  (h.height_schedule.height u)).T)) :=
    fun u =>
      zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel_integrable_restrict_Icc
        f F.toContourFamily h
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
            zetaCompletedExplicitFormulaArchimedeanRightBinetMainKernel
              f F.toContourFamily t)
        atTop
        (𝓝 (∫ t : ℝ,
          zetaCompletedExplicitFormulaArchimedeanRightBinetMainKernel
            f F.toContourFamily t)) :=
    zetaCompletedExplicitFormulaArchimedeanRightBinetMainKernel_scheduledWindow_tendsto_integral
      f F h
  let hmain :
      Tendsto
        (fun u : ℝ =>
          ∫ t in Set.Icc
              (-(F.toContourFamily.rectangle
                  (h.height_schedule.height u)).T)
              (F.toContourFamily.rectangle
                  (h.height_schedule.height u)).T,
            zetaCompletedExplicitFormulaArchimedeanRightBinetMainKernel
              f F.toContourFamily t)
        atTop
        (𝓝 (zetaCompletedExplicitFormulaPhi f 0)) :=
    Eq.subst
      (motive := fun z : ℂ =>
        Tendsto
          (fun u : ℝ =>
            ∫ t in Set.Icc
                (-(F.toContourFamily.rectangle
                    (h.height_schedule.height u)).T)
                (F.toContourFamily.rectangle
                    (h.height_schedule.height u)).T,
              zetaCompletedExplicitFormulaArchimedeanRightBinetMainKernel
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
            zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel
              f F.toContourFamily t)
        atTop
        (𝓝 (∫ t : ℝ,
          zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel
            f F.toContourFamily t)) :=
    zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel_scheduledWindow_tendsto_integral
      f F h
  let hremainder :
      Tendsto
        (fun u : ℝ =>
          ∫ t in Set.Icc
              (-(F.toContourFamily.rectangle
                  (h.height_schedule.height u)).T)
              (F.toContourFamily.rectangle
                  (h.height_schedule.height u)).T,
            zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel
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
              zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel
                f F.toContourFamily t)
          atTop
          (𝓝 z))
      hremainder_value
      hremainder_integral
  zetaCompletedExplicitFormulaArchimedeanRightAffineKernel_scheduledWindow_tendsto_phiZero_of_binetMain_remainder_branch
    f F h hbranch hmain_integrable hremainder_integrable hmain hremainder

/-- Branch-coherence form of right archimedean affine-kernel integrability. -/
theorem zetaCompletedExplicitFormulaArchimedeanRightAffineKernel_integrable_ownerBranchBinetLineValue
    (f : ZetaAdmissibleFunction)
    (F : ExplicitFormulaVerticallyRegularContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F.toContourFamily)
    (hbranch : Complex.binetBranchLogGammaCoherence) :
    Integrable
      (zetaCompletedExplicitFormulaArchimedeanRightAffineKernel
        f F.toContourFamily)
      (volume : Measure ℝ) :=
  Eq.subst
    (motive := fun branchData : Complex.binetBranchLogGammaCoherence =>
      Integrable
        (zetaCompletedExplicitFormulaArchimedeanRightAffineKernel
          f F.toContourFamily)
        (volume : Measure ℝ))
    (Eq.refl hbranch)
    (let hmain :
        Integrable
          (zetaCompletedExplicitFormulaArchimedeanRightBinetMainKernel
            f F.toContourFamily)
          (volume : Measure ℝ) :=
        zetaCompletedExplicitFormulaArchimedeanRightBinetMainKernel_integrable
          f F.toContourFamily h
      let hremainder :
        Integrable
          (zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel
            f F.toContourFamily)
          (volume : Measure ℝ) :=
        zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel_integrable
          f F.toContourFamily h
      let hsum :
        Integrable
          (fun t : ℝ =>
            zetaCompletedExplicitFormulaArchimedeanRightBinetMainKernel
              f F.toContourFamily t +
              zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel
                f F.toContourFamily t)
          (volume : Measure ℝ) :=
        hmain.add hremainder
      let hpoint :
        (zetaCompletedExplicitFormulaArchimedeanRightAffineKernel
          f F.toContourFamily) =ᵐ[volume]
          fun t : ℝ =>
            zetaCompletedExplicitFormulaArchimedeanRightBinetMainKernel
              f F.toContourFamily t +
              zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel
                f F.toContourFamily t :=
        Filter.Eventually.of_forall
          (fun t =>
            zetaCompletedExplicitFormulaArchimedeanRightAffineKernel_eq_binetMain_add_remainder
              f F.toContourFamily t)
      hsum.congr hpoint.symm)

/-- Branch-coherence form of left archimedean affine-kernel integrability. -/
theorem zetaCompletedExplicitFormulaArchimedeanLeftAffineKernel_integrable_ownerBranchBinetLineValue
    (f : ZetaAdmissibleFunction)
    (F : ExplicitFormulaVerticallyRegularContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F.toContourFamily)
    (hbranch : Complex.binetBranchLogGammaCoherence) :
    Integrable
      (zetaCompletedExplicitFormulaArchimedeanLeftAffineKernel
        f F.toContourFamily)
      (volume : Measure ℝ) :=
  Eq.subst
    (motive := fun branchData : Complex.binetBranchLogGammaCoherence =>
      Integrable
        (zetaCompletedExplicitFormulaArchimedeanLeftAffineKernel
          f F.toContourFamily)
        (volume : Measure ℝ))
    (Eq.refl hbranch)
    (let hregular :
        zetaCompletedExplicitFormulaLeftAffineLineGammaRegular
          F.toContourFamily :=
        zetaCompletedExplicitFormulaLeftAffineLineGammaRegular_of_verticallyRegular
          F
      let hmain :
        Integrable
          (zetaCompletedExplicitFormulaArchimedeanLeftBinetMainKernel
            f F.toContourFamily)
          (volume : Measure ℝ) :=
        zetaCompletedExplicitFormulaArchimedeanLeftBinetMainKernel_integrable
          f F.toContourFamily h hregular
      let hremainder :
        Integrable
          (zetaCompletedExplicitFormulaArchimedeanLeftBinetRemainderKernel
            f F.toContourFamily)
          (volume : Measure ℝ) :=
        zetaCompletedExplicitFormulaArchimedeanLeftBinetRemainderKernel_integrable
          f F.toContourFamily h hregular
      let hsum :
        Integrable
          (fun t : ℝ =>
            zetaCompletedExplicitFormulaArchimedeanLeftBinetMainKernel
              f F.toContourFamily t +
              zetaCompletedExplicitFormulaArchimedeanLeftBinetRemainderKernel
                f F.toContourFamily t)
          (volume : Measure ℝ) :=
        hmain.add hremainder
      let hpoint :
        (zetaCompletedExplicitFormulaArchimedeanLeftAffineKernel
          f F.toContourFamily) =ᵐ[volume]
          fun t : ℝ =>
            zetaCompletedExplicitFormulaArchimedeanLeftBinetMainKernel
              f F.toContourFamily t +
              zetaCompletedExplicitFormulaArchimedeanLeftBinetRemainderKernel
                f F.toContourFamily t :=
        Filter.Eventually.of_forall
          (fun t =>
            zetaCompletedExplicitFormulaArchimedeanLeftAffineKernel_eq_binetMain_add_remainder
              f F.toContourFamily hregular t)
      hsum.congr hpoint.symm)

/-- Branch-coherence form of scheduled right affine-window exhaustion. -/
theorem zetaCompletedExplicitFormulaArchimedeanRightAffineKernel_scheduledWindow_tendsto_integral_ownerBranchBinetLineValue
    (f : ZetaAdmissibleFunction)
    (F : ExplicitFormulaVerticallyRegularContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F.toContourFamily)
    (hbranch : Complex.binetBranchLogGammaCoherence) :
    Tendsto
      (fun u : ℝ =>
        ∫ t in Set.Icc
            (-(F.toContourFamily.rectangle (h.height_schedule.height u)).T)
            (F.toContourFamily.rectangle (h.height_schedule.height u)).T,
          zetaCompletedExplicitFormulaArchimedeanRightAffineKernel
            f F.toContourFamily t)
      atTop
      (𝓝 (∫ t : ℝ,
        zetaCompletedExplicitFormulaArchimedeanRightAffineKernel
          f F.toContourFamily t)) :=
  explicitFormulaScheduledRectangleWindowIntegral_tendsto_integral
    F.toContourFamily
    h.height_schedule.height
    (zetaCompletedExplicitFormulaArchimedeanRightAffineKernel
      f F.toContourFamily)
    h.height_schedule.cofinal
    (zetaCompletedExplicitFormulaArchimedeanRightAffineKernel_integrable_ownerBranchBinetLineValue
      f F h hbranch)

/-- Branch-coherence form of scheduled left affine-window exhaustion. -/
theorem zetaCompletedExplicitFormulaArchimedeanLeftAffineKernel_scheduledWindow_tendsto_integral_ownerBranchBinetLineValue
    (f : ZetaAdmissibleFunction)
    (F : ExplicitFormulaVerticallyRegularContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F.toContourFamily)
    (hbranch : Complex.binetBranchLogGammaCoherence) :
    Tendsto
      (fun u : ℝ =>
        ∫ t in Set.Icc
            (-(F.toContourFamily.rectangle (h.height_schedule.height u)).T)
            (F.toContourFamily.rectangle (h.height_schedule.height u)).T,
          zetaCompletedExplicitFormulaArchimedeanLeftAffineKernel
            f F.toContourFamily t)
      atTop
      (𝓝 (∫ t : ℝ,
        zetaCompletedExplicitFormulaArchimedeanLeftAffineKernel
          f F.toContourFamily t)) :=
  explicitFormulaScheduledRectangleWindowIntegral_tendsto_integral
    F.toContourFamily
    h.height_schedule.height
    (zetaCompletedExplicitFormulaArchimedeanLeftAffineKernel
      f F.toContourFamily)
    h.height_schedule.cofinal
    (zetaCompletedExplicitFormulaArchimedeanLeftAffineKernel_integrable_ownerBranchBinetLineValue
      f F h hbranch)

/-- Branch-coherence form of the scheduled right affine value theorem. -/
theorem zetaCompletedExplicitFormulaArchimedeanRightAffineKernel_scheduledWindow_tendsto_phiZero_of_fullLineAffineValue_branch
    (f : ZetaAdmissibleFunction)
    (F : ExplicitFormulaVerticallyRegularContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F.toContourFamily)
    (hbranch : Complex.binetBranchLogGammaCoherence)
    (hvalue :
      (∫ t : ℝ,
        zetaCompletedExplicitFormulaArchimedeanRightAffineKernel
          f F.toContourFamily t) =
        zetaCompletedExplicitFormulaPhi f 0) :
    Tendsto
      (fun u : ℝ =>
        ∫ t in Set.Icc
            (-(F.toContourFamily.rectangle (h.height_schedule.height u)).T)
            (F.toContourFamily.rectangle (h.height_schedule.height u)).T,
          zetaCompletedExplicitFormulaArchimedeanRightAffineKernel
            f F.toContourFamily t)
      atTop
      (𝓝 (zetaCompletedExplicitFormulaPhi f 0)) :=
  Eq.subst
    (motive := fun z : ℂ =>
      Tendsto
        (fun u : ℝ =>
          ∫ t in Set.Icc
              (-(F.toContourFamily.rectangle (h.height_schedule.height u)).T)
              (F.toContourFamily.rectangle (h.height_schedule.height u)).T,
            zetaCompletedExplicitFormulaArchimedeanRightAffineKernel
              f F.toContourFamily t)
        atTop
        (𝓝 z))
    hvalue
    (zetaCompletedExplicitFormulaArchimedeanRightAffineKernel_scheduledWindow_tendsto_integral_ownerBranchBinetLineValue
      f F h hbranch)

/-- Branch-coherence form of the scheduled left affine value theorem. -/
theorem zetaCompletedExplicitFormulaArchimedeanLeftAffineKernel_scheduledWindow_tendsto_neg_phiZero_of_fullLineAffineValue_branch
    (f : ZetaAdmissibleFunction)
    (F : ExplicitFormulaVerticallyRegularContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F.toContourFamily)
    (hbranch : Complex.binetBranchLogGammaCoherence)
    (hvalue :
      (∫ t : ℝ,
        zetaCompletedExplicitFormulaArchimedeanLeftAffineKernel
          f F.toContourFamily t) =
        -(zetaCompletedExplicitFormulaPhi f 0)) :
    Tendsto
      (fun u : ℝ =>
        ∫ t in Set.Icc
            (-(F.toContourFamily.rectangle (h.height_schedule.height u)).T)
            (F.toContourFamily.rectangle (h.height_schedule.height u)).T,
          zetaCompletedExplicitFormulaArchimedeanLeftAffineKernel
            f F.toContourFamily t)
      atTop
      (𝓝 (-(zetaCompletedExplicitFormulaPhi f 0))) :=
  Eq.subst
    (motive := fun z : ℂ =>
      Tendsto
        (fun u : ℝ =>
          ∫ t in Set.Icc
              (-(F.toContourFamily.rectangle (h.height_schedule.height u)).T)
              (F.toContourFamily.rectangle (h.height_schedule.height u)).T,
            zetaCompletedExplicitFormulaArchimedeanLeftAffineKernel
              f F.toContourFamily t)
        atTop
        (𝓝 z))
    hvalue
    (zetaCompletedExplicitFormulaArchimedeanLeftAffineKernel_scheduledWindow_tendsto_integral_ownerBranchBinetLineValue
      f F h hbranch)

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
