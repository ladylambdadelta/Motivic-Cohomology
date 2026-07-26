import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.ArchimedeanBranchBinetTransportLeft

/-!
# Branch Binet whole-line archimedean value transport

This file owns whole-line affine/Binet decomposition transports in the
branch-correct Gamma/Binet lane.
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

/-- Branch-coherence right whole-line affine value from full-line Binet values. -/
theorem zetaCompletedExplicitFormulaArchimedeanRightAffineKernel_integral_eq_phiZero_of_fullLineBinetValues_branch
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
    (∫ t : ℝ,
      zetaCompletedExplicitFormulaArchimedeanRightAffineKernel
        f F.toContourFamily t) =
      zetaCompletedExplicitFormulaPhi f 0 :=
  explicitFormulaScheduledScalar_integral_eq_of_tendsto_integral_and_value
    (fun u : ℝ =>
      ∫ t in Set.Icc
          (-(F.toContourFamily.rectangle
              (h.height_schedule.height u)).T)
          (F.toContourFamily.rectangle
              (h.height_schedule.height u)).T,
        zetaCompletedExplicitFormulaArchimedeanRightAffineKernel
          f F.toContourFamily t)
    (∫ t : ℝ,
      zetaCompletedExplicitFormulaArchimedeanRightAffineKernel
        f F.toContourFamily t)
    (zetaCompletedExplicitFormulaPhi f 0)
    (zetaCompletedExplicitFormulaArchimedeanRightAffineKernel_scheduledWindow_tendsto_integral_ownerBranchBinetLineValue
      f F h hbranch)
    (zetaCompletedExplicitFormulaArchimedeanRightAffineKernel_scheduledWindow_tendsto_phiZero_of_fullLineBinetValues_branch
      f F h hbranch hmain_value hremainder_value)

/-- Branch-coherence left whole-line affine value from full-line Binet values. -/
theorem zetaCompletedExplicitFormulaArchimedeanLeftAffineKernel_integral_eq_neg_phiZero_of_fullLineBinetValues_branch
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
    (∫ t : ℝ,
      zetaCompletedExplicitFormulaArchimedeanLeftAffineKernel
        f F.toContourFamily t) =
      -(zetaCompletedExplicitFormulaPhi f 0) :=
  explicitFormulaScheduledScalar_integral_eq_of_tendsto_integral_and_value
    (fun u : ℝ =>
      ∫ t in Set.Icc
          (-(F.toContourFamily.rectangle
              (h.height_schedule.height u)).T)
          (F.toContourFamily.rectangle
              (h.height_schedule.height u)).T,
        zetaCompletedExplicitFormulaArchimedeanLeftAffineKernel
          f F.toContourFamily t)
    (∫ t : ℝ,
      zetaCompletedExplicitFormulaArchimedeanLeftAffineKernel
        f F.toContourFamily t)
    (-(zetaCompletedExplicitFormulaPhi f 0))
    (zetaCompletedExplicitFormulaArchimedeanLeftAffineKernel_scheduledWindow_tendsto_integral_ownerBranchBinetLineValue
      f F h hbranch)
    (zetaCompletedExplicitFormulaArchimedeanLeftAffineKernel_scheduledWindow_tendsto_neg_phiZero_of_fullLineBinetValues_branch
      f F h hbranch hmain_value hremainder_value)

/-- Branch-coherence right whole-line affine/Binet decomposition. -/
theorem zetaCompletedExplicitFormulaArchimedeanRightAffineKernel_integral_eq_binetMain_add_remainder_integrals_branch
    (f : ZetaAdmissibleFunction)
    (F : ExplicitFormulaVerticallyRegularContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F.toContourFamily)
    (hbranch : Complex.binetBranchLogGammaCoherence) :
    (∫ t : ℝ,
      zetaCompletedExplicitFormulaArchimedeanRightAffineKernel
        f F.toContourFamily t) =
      (∫ t : ℝ,
        zetaCompletedExplicitFormulaArchimedeanRightBinetMainKernel
          f F.toContourFamily t) +
        ∫ t : ℝ,
          zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel
            f F.toContourFamily t :=
  Eq.subst
    (motive := fun branchData : Complex.binetBranchLogGammaCoherence =>
      (∫ t : ℝ,
        zetaCompletedExplicitFormulaArchimedeanRightAffineKernel
          f F.toContourFamily t) =
        (∫ t : ℝ,
          zetaCompletedExplicitFormulaArchimedeanRightBinetMainKernel
            f F.toContourFamily t) +
          ∫ t : ℝ,
            zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel
              f F.toContourFamily t)
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
        (∫ t : ℝ,
          zetaCompletedExplicitFormulaArchimedeanRightBinetMainKernel
            f F.toContourFamily t +
            zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel
              f F.toContourFamily t) =
          (∫ t : ℝ,
            zetaCompletedExplicitFormulaArchimedeanRightBinetMainKernel
              f F.toContourFamily t) +
            ∫ t : ℝ,
              zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel
                f F.toContourFamily t :=
        integral_add hmain hremainder
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
      Eq.trans (integral_congr_ae hpoint) hsum)

/-- Branch-coherence left whole-line affine/Binet decomposition. -/
theorem zetaCompletedExplicitFormulaArchimedeanLeftAffineKernel_integral_eq_binetMain_add_remainder_integrals_branch
    (f : ZetaAdmissibleFunction)
    (F : ExplicitFormulaVerticallyRegularContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F.toContourFamily)
    (hbranch : Complex.binetBranchLogGammaCoherence) :
    (∫ t : ℝ,
      zetaCompletedExplicitFormulaArchimedeanLeftAffineKernel
        f F.toContourFamily t) =
      (∫ t : ℝ,
        zetaCompletedExplicitFormulaArchimedeanLeftBinetMainKernel
          f F.toContourFamily t) +
        ∫ t : ℝ,
          zetaCompletedExplicitFormulaArchimedeanLeftBinetRemainderKernel
            f F.toContourFamily t :=
  Eq.subst
    (motive := fun branchData : Complex.binetBranchLogGammaCoherence =>
      (∫ t : ℝ,
        zetaCompletedExplicitFormulaArchimedeanLeftAffineKernel
          f F.toContourFamily t) =
        (∫ t : ℝ,
          zetaCompletedExplicitFormulaArchimedeanLeftBinetMainKernel
            f F.toContourFamily t) +
          ∫ t : ℝ,
            zetaCompletedExplicitFormulaArchimedeanLeftBinetRemainderKernel
              f F.toContourFamily t)
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
        (∫ t : ℝ,
          zetaCompletedExplicitFormulaArchimedeanLeftBinetMainKernel
            f F.toContourFamily t +
            zetaCompletedExplicitFormulaArchimedeanLeftBinetRemainderKernel
              f F.toContourFamily t) =
          (∫ t : ℝ,
            zetaCompletedExplicitFormulaArchimedeanLeftBinetMainKernel
              f F.toContourFamily t) +
            ∫ t : ℝ,
              zetaCompletedExplicitFormulaArchimedeanLeftBinetRemainderKernel
                f F.toContourFamily t :=
        integral_add hmain hremainder
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
      Eq.trans (integral_congr_ae hpoint) hsum)

/-- Branch-coherence right coupled Binet value from a right affine value. -/
theorem zetaCompletedExplicitFormulaArchimedeanRightBinetFullTransform_integral_eq_phiZero_of_affineValue_branch
    (f : ZetaAdmissibleFunction)
    (F : ExplicitFormulaVerticallyRegularContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F.toContourFamily)
    (hbranch : Complex.binetBranchLogGammaCoherence)
    (haffine :
      (∫ t : ℝ,
        zetaCompletedExplicitFormulaArchimedeanRightAffineKernel
          f F.toContourFamily t) =
        zetaCompletedExplicitFormulaPhi f 0) :
    (∫ t : ℝ,
      zetaCompletedExplicitFormulaArchimedeanRightBinetMainKernel
        f F.toContourFamily t) +
      ∫ t : ℝ,
        zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel
          f F.toContourFamily t =
      zetaCompletedExplicitFormulaPhi f 0 :=
  let hdecomp :
      (∫ t : ℝ,
        zetaCompletedExplicitFormulaArchimedeanRightAffineKernel
          f F.toContourFamily t) =
        (∫ t : ℝ,
          zetaCompletedExplicitFormulaArchimedeanRightBinetMainKernel
            f F.toContourFamily t) +
          ∫ t : ℝ,
            zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel
              f F.toContourFamily t :=
    zetaCompletedExplicitFormulaArchimedeanRightAffineKernel_integral_eq_binetMain_add_remainder_integrals_branch
      f F h hbranch
  Eq.trans hdecomp.symm haffine

/-- Branch-coherence left coupled Binet value from a left affine value with an
arbitrary scalar target. -/
theorem zetaCompletedExplicitFormulaArchimedeanLeftBinetFullTransform_integral_eq_of_affineValue_branch
    (f : ZetaAdmissibleFunction)
    (F : ExplicitFormulaVerticallyRegularContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F.toContourFamily)
    (hbranch : Complex.binetBranchLogGammaCoherence)
    (target : ℂ)
    (haffine :
      (∫ t : ℝ,
        zetaCompletedExplicitFormulaArchimedeanLeftAffineKernel
          f F.toContourFamily t) =
        target) :
    (∫ t : ℝ,
      zetaCompletedExplicitFormulaArchimedeanLeftBinetMainKernel
        f F.toContourFamily t) +
      ∫ t : ℝ,
        zetaCompletedExplicitFormulaArchimedeanLeftBinetRemainderKernel
          f F.toContourFamily t =
      target :=
  let hdecomp :
      (∫ t : ℝ,
        zetaCompletedExplicitFormulaArchimedeanLeftAffineKernel
          f F.toContourFamily t) =
        (∫ t : ℝ,
          zetaCompletedExplicitFormulaArchimedeanLeftBinetMainKernel
            f F.toContourFamily t) +
          ∫ t : ℝ,
            zetaCompletedExplicitFormulaArchimedeanLeftBinetRemainderKernel
              f F.toContourFamily t :=
    zetaCompletedExplicitFormulaArchimedeanLeftAffineKernel_integral_eq_binetMain_add_remainder_integrals_branch
      f F h hbranch
  Eq.trans hdecomp.symm haffine

/-- Branch-coherence left coupled Binet value from a left affine value. -/
theorem zetaCompletedExplicitFormulaArchimedeanLeftBinetFullTransform_integral_eq_neg_phiZero_of_affineValue_branch
    (f : ZetaAdmissibleFunction)
    (F : ExplicitFormulaVerticallyRegularContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F.toContourFamily)
    (hbranch : Complex.binetBranchLogGammaCoherence)
    (haffine :
      (∫ t : ℝ,
        zetaCompletedExplicitFormulaArchimedeanLeftAffineKernel
          f F.toContourFamily t) =
        -(zetaCompletedExplicitFormulaPhi f 0)) :
    (∫ t : ℝ,
      zetaCompletedExplicitFormulaArchimedeanLeftBinetMainKernel
        f F.toContourFamily t) +
      ∫ t : ℝ,
        zetaCompletedExplicitFormulaArchimedeanLeftBinetRemainderKernel
          f F.toContourFamily t =
      -(zetaCompletedExplicitFormulaPhi f 0) :=
  let hdecomp :
      (∫ t : ℝ,
        zetaCompletedExplicitFormulaArchimedeanLeftAffineKernel
          f F.toContourFamily t) =
        (∫ t : ℝ,
          zetaCompletedExplicitFormulaArchimedeanLeftBinetMainKernel
            f F.toContourFamily t) +
          ∫ t : ℝ,
            zetaCompletedExplicitFormulaArchimedeanLeftBinetRemainderKernel
              f F.toContourFamily t :=
    zetaCompletedExplicitFormulaArchimedeanLeftAffineKernel_integral_eq_binetMain_add_remainder_integrals_branch
      f F h hbranch
  Eq.trans hdecomp.symm haffine

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
