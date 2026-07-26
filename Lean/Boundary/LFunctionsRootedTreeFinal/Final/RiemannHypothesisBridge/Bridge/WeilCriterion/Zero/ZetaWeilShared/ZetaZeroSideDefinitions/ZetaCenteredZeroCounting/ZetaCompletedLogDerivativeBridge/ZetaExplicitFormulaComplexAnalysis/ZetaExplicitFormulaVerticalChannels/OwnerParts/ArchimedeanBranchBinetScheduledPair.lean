import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.ArchimedeanBranchTransport
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.ArchimedeanBranchBinetWholeLine

/-!
# Branch scheduled Binet pairs

This file owns the branch-coherence scheduled-pair transport for the
archimedean Binet full transforms.
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

/-- Branch right whole-line affine value from the scheduled right affine
window value. -/
theorem zetaCompletedExplicitFormulaArchimedeanRightAffineKernel_integral_eq_phiZero_of_scheduledWindow_branch
    (f : ZetaAdmissibleFunction)
    (F : ExplicitFormulaVerticallyRegularContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F.toContourFamily)
    (hbranch : Complex.binetBranchLogGammaCoherence)
    (hscheduled :
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
        (𝓝 (zetaCompletedExplicitFormulaPhi f 0))) :
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
    hscheduled

/-- Branch left whole-line affine value from the scheduled left affine window
value. -/
theorem zetaCompletedExplicitFormulaArchimedeanLeftAffineKernel_integral_eq_neg_phiZero_of_scheduledWindow_branch
    (f : ZetaAdmissibleFunction)
    (F : ExplicitFormulaVerticallyRegularContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F.toContourFamily)
    (hbranch : Complex.binetBranchLogGammaCoherence)
    (hscheduled :
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
        (𝓝 (-(zetaCompletedExplicitFormulaPhi f 0)))) :
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
    hscheduled

/-- Branch paired whole-line affine values from direct paired scheduled affine
window values. -/
theorem zetaCompletedExplicitFormulaArchimedeanAffineKernel_integral_pair_of_scheduledWindow_branch
    (f : ZetaAdmissibleFunction)
    (F : ExplicitFormulaVerticallyRegularContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F.toContourFamily)
    (hbranch : Complex.binetBranchLogGammaCoherence)
    (hscheduled :
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
        (𝓝 (zetaCompletedExplicitFormulaPhi f 0)) ∧
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
        (𝓝 (-(zetaCompletedExplicitFormulaPhi f 0)))) :
    ((∫ t : ℝ,
      zetaCompletedExplicitFormulaArchimedeanRightAffineKernel
        f F.toContourFamily t) =
      zetaCompletedExplicitFormulaPhi f 0) ∧
    ((∫ t : ℝ,
      zetaCompletedExplicitFormulaArchimedeanLeftAffineKernel
        f F.toContourFamily t) =
      -(zetaCompletedExplicitFormulaPhi f 0)) :=
  And.intro
    (zetaCompletedExplicitFormulaArchimedeanRightAffineKernel_integral_eq_phiZero_of_scheduledWindow_branch
      f F h hbranch hscheduled.1)
    (zetaCompletedExplicitFormulaArchimedeanLeftAffineKernel_integral_eq_neg_phiZero_of_scheduledWindow_branch
      f F h hbranch hscheduled.2)

/-- Branch paired scheduled Gamma/Binet full-transform values from affine
whole-line values. -/
theorem zetaCompletedExplicitFormulaArchimedeanBinetFullTransform_scheduledPair_of_affineValues_branch
    (f : ZetaAdmissibleFunction)
    (F : ExplicitFormulaVerticallyRegularContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F.toContourFamily)
    (hbranch : Complex.binetBranchLogGammaCoherence)
    (hright_affine :
      (∫ t : ℝ,
        zetaCompletedExplicitFormulaArchimedeanRightAffineKernel
          f F.toContourFamily t) =
        zetaCompletedExplicitFormulaPhi f 0)
    (hleft_affine :
      (∫ t : ℝ,
        zetaCompletedExplicitFormulaArchimedeanLeftAffineKernel
          f F.toContourFamily t) =
        -(zetaCompletedExplicitFormulaPhi f 0)) :
    (Tendsto
        (fun u : ℝ =>
          (∫ t in Set.Icc
              (-(F.toContourFamily.rectangle
                  (h.height_schedule.height u)).T)
              (F.toContourFamily.rectangle
                  (h.height_schedule.height u)).T,
            zetaCompletedExplicitFormulaArchimedeanRightBinetMainKernel
              f F.toContourFamily t) +
            ∫ t in Set.Icc
              (-(F.toContourFamily.rectangle
                  (h.height_schedule.height u)).T)
              (F.toContourFamily.rectangle
                  (h.height_schedule.height u)).T,
            zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel
              f F.toContourFamily t)
        atTop
        (𝓝 (zetaCompletedExplicitFormulaPhi f 0))) ∧
      (Tendsto
        (fun u : ℝ =>
          (∫ t in Set.Icc
              (-(F.toContourFamily.rectangle
                  (h.height_schedule.height u)).T)
              (F.toContourFamily.rectangle
                  (h.height_schedule.height u)).T,
            zetaCompletedExplicitFormulaArchimedeanLeftBinetMainKernel
              f F.toContourFamily t) +
            ∫ t in Set.Icc
              (-(F.toContourFamily.rectangle
                  (h.height_schedule.height u)).T)
              (F.toContourFamily.rectangle
                  (h.height_schedule.height u)).T,
            zetaCompletedExplicitFormulaArchimedeanLeftBinetRemainderKernel
              f F.toContourFamily t)
        atTop
        (𝓝 (-(zetaCompletedExplicitFormulaPhi f 0)))) :=
  zetaCompletedExplicitFormulaArchimedeanBinetFullTransform_scheduledPair_of_fullTransformIntegralValues
    f F h
    (zetaCompletedExplicitFormulaArchimedeanRightBinetFullTransform_integral_eq_phiZero_of_affineValue_branch
      f F h hbranch hright_affine)
    (zetaCompletedExplicitFormulaArchimedeanLeftBinetFullTransform_integral_eq_neg_phiZero_of_affineValue_branch
      f F h hbranch hleft_affine)

/-- Branch paired scheduled Gamma/Binet full-transform values from direct
paired scheduled affine contour values. -/
theorem zetaCompletedExplicitFormulaArchimedeanBinetFullTransform_scheduledPair_of_scheduledAffineValues_branch
    (f : ZetaAdmissibleFunction)
    (F : ExplicitFormulaVerticallyRegularContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F.toContourFamily)
    (hbranch : Complex.binetBranchLogGammaCoherence)
    (hscheduled :
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
        (𝓝 (zetaCompletedExplicitFormulaPhi f 0)) ∧
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
        (𝓝 (-(zetaCompletedExplicitFormulaPhi f 0)))) :
    (Tendsto
        (fun u : ℝ =>
          (∫ t in Set.Icc
              (-(F.toContourFamily.rectangle
                  (h.height_schedule.height u)).T)
              (F.toContourFamily.rectangle
                  (h.height_schedule.height u)).T,
            zetaCompletedExplicitFormulaArchimedeanRightBinetMainKernel
              f F.toContourFamily t) +
            ∫ t in Set.Icc
              (-(F.toContourFamily.rectangle
                  (h.height_schedule.height u)).T)
              (F.toContourFamily.rectangle
                  (h.height_schedule.height u)).T,
            zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel
              f F.toContourFamily t)
        atTop
        (𝓝 (zetaCompletedExplicitFormulaPhi f 0))) ∧
      (Tendsto
        (fun u : ℝ =>
          (∫ t in Set.Icc
              (-(F.toContourFamily.rectangle
                  (h.height_schedule.height u)).T)
              (F.toContourFamily.rectangle
                  (h.height_schedule.height u)).T,
            zetaCompletedExplicitFormulaArchimedeanLeftBinetMainKernel
              f F.toContourFamily t) +
            ∫ t in Set.Icc
              (-(F.toContourFamily.rectangle
                  (h.height_schedule.height u)).T)
              (F.toContourFamily.rectangle
                  (h.height_schedule.height u)).T,
            zetaCompletedExplicitFormulaArchimedeanLeftBinetRemainderKernel
              f F.toContourFamily t)
        atTop
        (𝓝 (-(zetaCompletedExplicitFormulaPhi f 0)))) :=
  zetaCompletedExplicitFormulaArchimedeanBinetFullTransform_scheduledPair_of_affineValues_branch
    f F h hbranch
    (zetaCompletedExplicitFormulaArchimedeanAffineKernel_integral_pair_of_scheduledWindow_branch
      f F h hbranch hscheduled).1
    (zetaCompletedExplicitFormulaArchimedeanAffineKernel_integral_pair_of_scheduledWindow_branch
      f F h hbranch hscheduled).2

/-- Branch paired scheduled Gamma/Binet full-transform values from paired
scheduled affine contour values, preserving an arbitrary left target. -/
theorem zetaCompletedExplicitFormulaArchimedeanBinetFullTransform_scheduledPair_of_scheduledAffineValues_leftTarget_branch
    (f : ZetaAdmissibleFunction)
    (F : ExplicitFormulaVerticallyRegularContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F.toContourFamily)
    (hbranch : Complex.binetBranchLogGammaCoherence)
    (leftTarget : ℂ)
    (hscheduled :
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
        (𝓝 (zetaCompletedExplicitFormulaPhi f 0)) ∧
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
        (𝓝 leftTarget)) :
    (Tendsto
        (fun u : ℝ =>
          (∫ t in Set.Icc
              (-(F.toContourFamily.rectangle
                  (h.height_schedule.height u)).T)
              (F.toContourFamily.rectangle
                  (h.height_schedule.height u)).T,
            zetaCompletedExplicitFormulaArchimedeanRightBinetMainKernel
              f F.toContourFamily t) +
            ∫ t in Set.Icc
              (-(F.toContourFamily.rectangle
                  (h.height_schedule.height u)).T)
              (F.toContourFamily.rectangle
                  (h.height_schedule.height u)).T,
            zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel
              f F.toContourFamily t)
        atTop
        (𝓝 (zetaCompletedExplicitFormulaPhi f 0))) ∧
      (Tendsto
        (fun u : ℝ =>
          (∫ t in Set.Icc
              (-(F.toContourFamily.rectangle
                  (h.height_schedule.height u)).T)
              (F.toContourFamily.rectangle
                  (h.height_schedule.height u)).T,
            zetaCompletedExplicitFormulaArchimedeanLeftBinetMainKernel
              f F.toContourFamily t) +
            ∫ t in Set.Icc
              (-(F.toContourFamily.rectangle
                  (h.height_schedule.height u)).T)
              (F.toContourFamily.rectangle
                  (h.height_schedule.height u)).T,
            zetaCompletedExplicitFormulaArchimedeanLeftBinetRemainderKernel
              f F.toContourFamily t)
        atTop
        (𝓝 leftTarget)) :=
  let hright_affine :
      (∫ t : ℝ,
        zetaCompletedExplicitFormulaArchimedeanRightAffineKernel
          f F.toContourFamily t) =
        zetaCompletedExplicitFormulaPhi f 0 :=
    zetaCompletedExplicitFormulaArchimedeanRightAffineKernel_integral_eq_phiZero_of_scheduledWindow_branch
      f F h hbranch hscheduled.1
  let hleft_affine :
      (∫ t : ℝ,
        zetaCompletedExplicitFormulaArchimedeanLeftAffineKernel
          f F.toContourFamily t) =
        leftTarget :=
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
      leftTarget
      (zetaCompletedExplicitFormulaArchimedeanLeftAffineKernel_scheduledWindow_tendsto_integral_ownerBranchBinetLineValue
        f F h hbranch)
      hscheduled.2
  let hright_binet :
      (∫ t : ℝ,
        zetaCompletedExplicitFormulaArchimedeanRightBinetMainKernel
          f F.toContourFamily t) +
        ∫ t : ℝ,
          zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel
            f F.toContourFamily t =
        zetaCompletedExplicitFormulaPhi f 0 :=
    zetaCompletedExplicitFormulaArchimedeanRightBinetFullTransform_integral_eq_phiZero_of_affineValue_branch
      f F h hbranch hright_affine
  let hleft_binet :
      (∫ t : ℝ,
        zetaCompletedExplicitFormulaArchimedeanLeftBinetMainKernel
          f F.toContourFamily t) +
        ∫ t : ℝ,
          zetaCompletedExplicitFormulaArchimedeanLeftBinetRemainderKernel
            f F.toContourFamily t =
        leftTarget :=
    zetaCompletedExplicitFormulaArchimedeanLeftBinetFullTransform_integral_eq_of_affineValue_branch
      f F h hbranch leftTarget hleft_affine
  zetaCompletedExplicitFormulaArchimedeanBinetFullTransform_scheduledPair_of_fullTransformIntegralValues_leftTarget
    f F h leftTarget hright_binet hleft_binet

/-- Branch paired scheduled Gamma/Binet full-transform values from a right
scheduled affine value and the inverse-Gamma difference normalization. -/
theorem zetaCompletedExplicitFormulaArchimedeanBinetFullTransform_scheduledPair_of_rightAffineScheduled_and_inverseGammaDifferenceValue_branch
    (f : ZetaAdmissibleFunction)
    (F : ExplicitFormulaVerticallyRegularContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F.toContourFamily)
    (hbranch : Complex.binetBranchLogGammaCoherence)
    (hright :
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
    (hvalue :
      (∫ t : ℝ,
        zetaCompletedExplicitFormulaInverseGammaDifferenceAffineKernel
          f F.toContourFamily t) =
        zetaCompletedExplicitFormulaArchimedeanContribution f +
          zetaCompletedExplicitFormulaCorrectionStandardContourContribution f) :
    (Tendsto
        (fun u : ℝ =>
          (∫ t in Set.Icc
              (-(F.toContourFamily.rectangle
                  (h.height_schedule.height u)).T)
              (F.toContourFamily.rectangle
                  (h.height_schedule.height u)).T,
            zetaCompletedExplicitFormulaArchimedeanRightBinetMainKernel
              f F.toContourFamily t) +
            ∫ t in Set.Icc
              (-(F.toContourFamily.rectangle
                  (h.height_schedule.height u)).T)
              (F.toContourFamily.rectangle
                  (h.height_schedule.height u)).T,
            zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel
              f F.toContourFamily t)
        atTop
        (𝓝 (zetaCompletedExplicitFormulaPhi f 0))) ∧
      (Tendsto
        (fun u : ℝ =>
          (∫ t in Set.Icc
              (-(F.toContourFamily.rectangle
                  (h.height_schedule.height u)).T)
              (F.toContourFamily.rectangle
                  (h.height_schedule.height u)).T,
            zetaCompletedExplicitFormulaArchimedeanLeftBinetMainKernel
              f F.toContourFamily t) +
            ∫ t in Set.Icc
              (-(F.toContourFamily.rectangle
                  (h.height_schedule.height u)).T)
              (F.toContourFamily.rectangle
                  (h.height_schedule.height u)).T,
            zetaCompletedExplicitFormulaArchimedeanLeftBinetRemainderKernel
              f F.toContourFamily t)
        atTop
        (𝓝
          (zetaCompletedExplicitFormulaPhi f 0 -
            zetaCompletedExplicitFormulaArchimedeanContribution f))) :=
  zetaCompletedExplicitFormulaArchimedeanBinetFullTransform_scheduledPair_of_scheduledAffineValues_leftTarget_branch
    f F h hbranch
    (zetaCompletedExplicitFormulaPhi f 0 -
      zetaCompletedExplicitFormulaArchimedeanContribution f)
    (zetaCompletedExplicitFormulaArchimedeanAffineKernel_scheduledPair_of_right_and_verticallyRegular_branchBinet_integral_eq
      f F h hbranch hright hvalue)

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
