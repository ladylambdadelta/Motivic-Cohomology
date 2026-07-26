import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaAdmissibleTransformRegularity.ZetaPhiAnalyticControlCore
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaAdmissibleTransformRegularity.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.ArchimedeanVerticalAnalyticEstimates

/-!
# Archimedean vertical-channel transport estimate

This file owns the Gamma/completion vertical-channel transport estimate.  The
projection layer consumes this theorem but does not own its proof.
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

/-- Algebraic extraction of the archimedean packet from the inverse-Gamma completion
packet and the correction packet along the scheduled contour heights.

The analytic content remains in the two input limits.  This lemma only transports
the already proved fixed-height identity
`inverseGammaCompletion = archimedean + correction` through `Tendsto`. -/
theorem zetaCompletedExplicitFormulaArchimedeanVerticalChannel_tendsto_of_inverseGammaCompletion_and_correction
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (hinverse :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaInverseGammaCompletionVerticalChannel
            f F (h.height_schedule.height u))
        atTop
        (𝓝
          (zetaCompletedExplicitFormulaArchimedeanContribution f +
            zetaCompletedExplicitFormulaCorrectionStandardContourContribution f)))
    (hcorrection :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaCorrectionVerticalChannel
            f F (h.height_schedule.height u))
        atTop
        (𝓝 (zetaCompletedExplicitFormulaCorrectionStandardContourContribution f))) :
    Tendsto
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaArchimedeanVerticalChannel
          f F (h.height_schedule.height u))
      atTop
      (𝓝 (zetaCompletedExplicitFormulaArchimedeanContribution f)) := by
  let A : ℂ := zetaCompletedExplicitFormulaArchimedeanContribution f
  let C : ℂ := zetaCompletedExplicitFormulaCorrectionStandardContourContribution f
  have hdiff :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaInverseGammaCompletionVerticalChannel
              f F (h.height_schedule.height u) -
            zetaCompletedExplicitFormulaCorrectionVerticalChannel
              f F (h.height_schedule.height u))
        atTop
        (𝓝 ((A + C) - C)) :=
    hinverse.sub hcorrection
  have htarget : (A + C) - C = A := by
    exact add_sub_cancel_right A C
  have harch_fun :
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaArchimedeanVerticalChannel
          f F (h.height_schedule.height u)) =
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaInverseGammaCompletionVerticalChannel
            f F (h.height_schedule.height u) -
          zetaCompletedExplicitFormulaCorrectionVerticalChannel
            f F (h.height_schedule.height u)) := by
    funext u
    let T : ℝ := h.height_schedule.height u
    let A_u : ℂ := zetaCompletedExplicitFormulaArchimedeanVerticalChannel f F T
    let C_u : ℂ := zetaCompletedExplicitFormulaCorrectionVerticalChannel f F T
    let G_u : ℂ := zetaCompletedExplicitFormulaInverseGammaCompletionVerticalChannel f F T
    have hdecomp : G_u = A_u + C_u :=
      zetaCompletedExplicitFormulaInverseGammaCompletionVerticalChannel_eq_archimedean_add_correction
        f h.phi_control F T (h.height_schedule.avoids_boundary u)
    change A_u = G_u - C_u
    calc
      A_u = A_u + C_u - C_u := by
        exact (add_sub_cancel_right A_u C_u).symm
      _ = G_u - C_u := by
        exact congrArg (fun z : ℂ => z - C_u) hdecomp.symm
  exact Eq.subst
    (motive := fun φ : ℝ → ℂ =>
      Tendsto φ atTop (𝓝 (zetaCompletedExplicitFormulaArchimedeanContribution f)))
    harch_fun.symm
    (Eq.subst
      (motive := fun z : ℂ =>
        Tendsto
          (fun u : ℝ =>
            zetaCompletedExplicitFormulaInverseGammaCompletionVerticalChannel
                f F (h.height_schedule.height u) -
              zetaCompletedExplicitFormulaCorrectionVerticalChannel
                f F (h.height_schedule.height u))
          atTop
          (𝓝 z))
      htarget
      hdiff)

/-- Algebraic extraction of the archimedean packet from the named scheduled
inverse-Gamma completion channel and named scheduled correction channel. -/
theorem zetaCompletedExplicitFormulaArchimedeanVerticalChannel_tendsto_of_scheduledInverseGammaCompletion_and_scheduledCorrection
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (hinverse :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaScheduledInverseGammaCompletionVerticalChannel
            f F h u)
        atTop
        (𝓝
          (zetaCompletedExplicitFormulaArchimedeanContribution f +
            zetaCompletedExplicitFormulaCorrectionStandardContourContribution f)))
    (hcorrection :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaScheduledCorrectionVerticalChannel
            f F h u)
        atTop
        (𝓝 (zetaCompletedExplicitFormulaCorrectionStandardContourContribution f))) :
    Tendsto
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaArchimedeanVerticalChannel
          f F (h.height_schedule.height u))
      atTop
      (𝓝 (zetaCompletedExplicitFormulaArchimedeanContribution f)) := by
  let A : ℂ := zetaCompletedExplicitFormulaArchimedeanContribution f
  let C : ℂ := zetaCompletedExplicitFormulaCorrectionStandardContourContribution f
  have hdiff :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaScheduledInverseGammaCompletionVerticalChannel
              f F h u -
            zetaCompletedExplicitFormulaScheduledCorrectionVerticalChannel
              f F h u)
        atTop
        (𝓝 ((A + C) - C)) :=
    hinverse.sub hcorrection
  have htarget : (A + C) - C = A := by
    exact add_sub_cancel_right A C
  have harch_fun :
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaArchimedeanVerticalChannel
          f F (h.height_schedule.height u)) =
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaScheduledInverseGammaCompletionVerticalChannel
            f F h u -
          zetaCompletedExplicitFormulaScheduledCorrectionVerticalChannel
            f F h u) := by
    funext u
    exact
      zetaCompletedExplicitFormulaScheduledArchimedean_eq_inverseGammaCompletion_sub_correction
        f F h u
  exact Eq.subst
    (motive := fun φ : ℝ → ℂ =>
      Tendsto φ atTop (𝓝 (zetaCompletedExplicitFormulaArchimedeanContribution f)))
    harch_fun.symm
    (Eq.subst
      (motive := fun z : ℂ =>
        Tendsto
          (fun u : ℝ =>
            zetaCompletedExplicitFormulaScheduledInverseGammaCompletionVerticalChannel
                f F h u -
              zetaCompletedExplicitFormulaScheduledCorrectionVerticalChannel
                f F h u)
          atTop
          (𝓝 z))
      htarget
      hdiff)

/-- Scheduled right-minus-left archimedean affine window convergence from the
archimedean vertical-channel convergence.

This theorem is only affine-normal-form transport.  The analytic content is the
input convergence of `zetaCompletedExplicitFormulaArchimedeanVerticalChannel`;
the conclusion names the actual right and shifted-left affine kernels. -/
theorem zetaCompletedExplicitFormulaArchimedeanDifferenceAffineKernel_scheduledWindow_tendsto_of_verticalChannel
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (hchannel :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaArchimedeanVerticalChannel
            f F (h.height_schedule.height u))
        atTop
        (𝓝 (zetaCompletedExplicitFormulaArchimedeanContribution f))) :
    Tendsto
      (fun u : ℝ =>
        (∫ t in Set.Icc
            (-(F.rectangle (h.height_schedule.height u)).T)
            (F.rectangle (h.height_schedule.height u)).T,
          zetaCompletedExplicitFormulaArchimedeanRightAffineKernel f F t) -
          ∫ t in Set.Icc
            (-(F.rectangle (h.height_schedule.height u)).T)
            (F.rectangle (h.height_schedule.height u)).T,
            zetaCompletedExplicitFormulaArchimedeanLeftAffineKernel f F t)
      atTop
      (𝓝 (zetaCompletedExplicitFormulaArchimedeanContribution f)) := by
  have hfun :
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaArchimedeanVerticalChannel
          f F (h.height_schedule.height u)) =
      (fun u : ℝ =>
        (∫ t in Set.Icc
            (-(F.rectangle (h.height_schedule.height u)).T)
            (F.rectangle (h.height_schedule.height u)).T,
          zetaCompletedExplicitFormulaArchimedeanRightAffineKernel f F t) -
          ∫ t in Set.Icc
            (-(F.rectangle (h.height_schedule.height u)).T)
            (F.rectangle (h.height_schedule.height u)).T,
            zetaCompletedExplicitFormulaArchimedeanLeftAffineKernel f F t) := by
    funext u
    exact
      zetaCompletedExplicitFormulaScheduledArchimedeanVerticalChannel_eq_affineKernelIntegrals
        f F h u
  exact
    Eq.subst
      (motive := fun φ : ℝ → ℂ =>
        Tendsto φ atTop
          (𝓝 (zetaCompletedExplicitFormulaArchimedeanContribution f)))
      hfun
      hchannel

/-- Paired one-sided scheduled affine values imply the scheduled
right-minus-left archimedean affine-window value.

This is only the algebraic subtraction of the two one-sided scheduled limits;
it does not identify that difference with the public archimedean contribution. -/
theorem zetaCompletedExplicitFormulaArchimedeanAffineWindowDifference_tendsto_of_scheduledPair
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (hscheduled :
      Tendsto
        (fun u : ℝ =>
          ∫ t in Set.Icc
              (-(F.rectangle (h.height_schedule.height u)).T)
              (F.rectangle (h.height_schedule.height u)).T,
            zetaCompletedExplicitFormulaArchimedeanRightAffineKernel f F t)
        atTop
        (𝓝 (zetaCompletedExplicitFormulaPhi f 0)) ∧
      Tendsto
        (fun u : ℝ =>
          ∫ t in Set.Icc
              (-(F.rectangle (h.height_schedule.height u)).T)
              (F.rectangle (h.height_schedule.height u)).T,
            zetaCompletedExplicitFormulaArchimedeanLeftAffineKernel f F t)
        atTop
        (𝓝 (-(zetaCompletedExplicitFormulaPhi f 0)))) :
    Tendsto
      (fun u : ℝ =>
        (∫ t in Set.Icc
            (-(F.rectangle (h.height_schedule.height u)).T)
            (F.rectangle (h.height_schedule.height u)).T,
          zetaCompletedExplicitFormulaArchimedeanRightAffineKernel f F t) -
          ∫ t in Set.Icc
            (-(F.rectangle (h.height_schedule.height u)).T)
            (F.rectangle (h.height_schedule.height u)).T,
            zetaCompletedExplicitFormulaArchimedeanLeftAffineKernel f F t)
      atTop
      (𝓝
        (zetaCompletedExplicitFormulaPhi f 0 -
          -(zetaCompletedExplicitFormulaPhi f 0))) := by
  let Phi0 : ℂ := zetaCompletedExplicitFormulaPhi f 0
  let Wright : ℝ → ℂ := fun u : ℝ =>
    ∫ t in Set.Icc
        (-(F.rectangle (h.height_schedule.height u)).T)
        (F.rectangle (h.height_schedule.height u)).T,
      zetaCompletedExplicitFormulaArchimedeanRightAffineKernel f F t
  let Wleft : ℝ → ℂ := fun u : ℝ =>
    ∫ t in Set.Icc
        (-(F.rectangle (h.height_schedule.height u)).T)
        (F.rectangle (h.height_schedule.height u)).T,
      zetaCompletedExplicitFormulaArchimedeanLeftAffineKernel f F t
  have hdiff :
      Tendsto (fun u : ℝ => Wright u - Wleft u) atTop (𝓝 (Phi0 - -Phi0)) :=
    hscheduled.1.sub hscheduled.2
  exact hdiff

/-- Left scheduled affine value from the right scheduled affine value and the
right-minus-left scheduled affine-window value.

This is a non-symmetric algebraic reduction. It does not identify the public
archimedean contribution with a doubled one-sided value. -/
theorem zetaCompletedExplicitFormulaArchimedeanLeftAffineKernel_scheduledWindow_tendsto_neg_phiZero_of_right_and_difference
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (hright :
      Tendsto
        (fun u : ℝ =>
          ∫ t in Set.Icc
              (-(F.rectangle (h.height_schedule.height u)).T)
              (F.rectangle (h.height_schedule.height u)).T,
            zetaCompletedExplicitFormulaArchimedeanRightAffineKernel f F t)
        atTop
        (𝓝 (zetaCompletedExplicitFormulaPhi f 0)))
    (hdifference :
      Tendsto
        (fun u : ℝ =>
          (∫ t in Set.Icc
              (-(F.rectangle (h.height_schedule.height u)).T)
              (F.rectangle (h.height_schedule.height u)).T,
            zetaCompletedExplicitFormulaArchimedeanRightAffineKernel f F t) -
            ∫ t in Set.Icc
              (-(F.rectangle (h.height_schedule.height u)).T)
              (F.rectangle (h.height_schedule.height u)).T,
              zetaCompletedExplicitFormulaArchimedeanLeftAffineKernel f F t)
        atTop
        (𝓝 (zetaCompletedExplicitFormulaArchimedeanContribution f))) :
    Tendsto
      (fun u : ℝ =>
        ∫ t in Set.Icc
            (-(F.rectangle (h.height_schedule.height u)).T)
            (F.rectangle (h.height_schedule.height u)).T,
          zetaCompletedExplicitFormulaArchimedeanLeftAffineKernel f F t)
      atTop
      (𝓝
        (zetaCompletedExplicitFormulaPhi f 0 -
          zetaCompletedExplicitFormulaArchimedeanContribution f)) := by
  let Phi0 : ℂ := zetaCompletedExplicitFormulaPhi f 0
  let Wright : ℝ → ℂ := fun u : ℝ =>
    ∫ t in Set.Icc
        (-(F.rectangle (h.height_schedule.height u)).T)
        (F.rectangle (h.height_schedule.height u)).T,
      zetaCompletedExplicitFormulaArchimedeanRightAffineKernel f F t
  let Wleft : ℝ → ℂ := fun u : ℝ =>
    ∫ t in Set.Icc
        (-(F.rectangle (h.height_schedule.height u)).T)
        (F.rectangle (h.height_schedule.height u)).T,
      zetaCompletedExplicitFormulaArchimedeanLeftAffineKernel f F t
  have hraw :
      Tendsto
        (fun u : ℝ => Wright u - (Wright u - Wleft u))
        atTop
        (𝓝 (Phi0 - zetaCompletedExplicitFormulaArchimedeanContribution f)) :=
    hright.sub hdifference
  have hfun :
      (fun u : ℝ => Wright u - (Wright u - Wleft u)) =
      (fun u : ℝ => Wleft u) := by
    funext u
    let R : ℂ := Wright u
    let L : ℂ := Wleft u
    calc
      R - (R - L) = R + -(R - L) := by
        exact sub_eq_add_neg R (R - L)
      _ = R + (-(R + -L)) := by
        exact congrArg (fun z : ℂ => R + -z) (sub_eq_add_neg R L)
      _ = R + (-R + -(-L)) := by
        exact congrArg (fun z : ℂ => R + z) (neg_add R (-L))
      _ = R + (-R + L) := by
        exact congrArg (fun z : ℂ => R + (-R + z)) (neg_neg L)
      _ = (R + -R) + L := by
        exact (add_assoc R (-R) L).symm
      _ = 0 + L := by
        exact congrArg (fun z : ℂ => z + L) (add_neg_cancel R)
      _ = L := by
        exact zero_add L
  exact
    Eq.subst
      (motive := fun φ : ℝ → ℂ =>
        Tendsto φ atTop
          (𝓝
            (zetaCompletedExplicitFormulaPhi f 0 -
              zetaCompletedExplicitFormulaArchimedeanContribution f)))
      hfun
      hraw

/-- Paired scheduled affine values from a right scheduled affine value and the
right-minus-left scheduled affine-window value.

This reduces the paired owner theorem to one genuinely one-sided contour value
plus the already owned difference-channel transport. -/
theorem zetaCompletedExplicitFormulaArchimedeanAffineKernel_scheduledPair_of_right_and_difference
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (hright :
      Tendsto
        (fun u : ℝ =>
          ∫ t in Set.Icc
              (-(F.rectangle (h.height_schedule.height u)).T)
              (F.rectangle (h.height_schedule.height u)).T,
            zetaCompletedExplicitFormulaArchimedeanRightAffineKernel f F t)
        atTop
        (𝓝 (zetaCompletedExplicitFormulaPhi f 0)))
    (hdifference :
      Tendsto
        (fun u : ℝ =>
          (∫ t in Set.Icc
              (-(F.rectangle (h.height_schedule.height u)).T)
              (F.rectangle (h.height_schedule.height u)).T,
            zetaCompletedExplicitFormulaArchimedeanRightAffineKernel f F t) -
            ∫ t in Set.Icc
              (-(F.rectangle (h.height_schedule.height u)).T)
              (F.rectangle (h.height_schedule.height u)).T,
              zetaCompletedExplicitFormulaArchimedeanLeftAffineKernel f F t)
        atTop
        (𝓝 (zetaCompletedExplicitFormulaArchimedeanContribution f))) :
    Tendsto
        (fun u : ℝ =>
          ∫ t in Set.Icc
              (-(F.rectangle (h.height_schedule.height u)).T)
              (F.rectangle (h.height_schedule.height u)).T,
            zetaCompletedExplicitFormulaArchimedeanRightAffineKernel f F t)
        atTop
        (𝓝 (zetaCompletedExplicitFormulaPhi f 0)) ∧
      Tendsto
        (fun u : ℝ =>
          ∫ t in Set.Icc
              (-(F.rectangle (h.height_schedule.height u)).T)
              (F.rectangle (h.height_schedule.height u)).T,
            zetaCompletedExplicitFormulaArchimedeanLeftAffineKernel f F t)
        atTop
        (𝓝
          (zetaCompletedExplicitFormulaPhi f 0 -
            zetaCompletedExplicitFormulaArchimedeanContribution f)) := by
  exact
    ⟨hright,
      zetaCompletedExplicitFormulaArchimedeanLeftAffineKernel_scheduledWindow_tendsto_neg_phiZero_of_right_and_difference
        f F h hright hdifference⟩

/-- Paired scheduled affine values from a right scheduled affine value and the
archimedean vertical-channel value. -/
theorem zetaCompletedExplicitFormulaArchimedeanAffineKernel_scheduledPair_of_right_and_verticalChannel
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (hright :
      Tendsto
        (fun u : ℝ =>
          ∫ t in Set.Icc
              (-(F.rectangle (h.height_schedule.height u)).T)
              (F.rectangle (h.height_schedule.height u)).T,
            zetaCompletedExplicitFormulaArchimedeanRightAffineKernel f F t)
        atTop
        (𝓝 (zetaCompletedExplicitFormulaPhi f 0)))
    (hchannel :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaArchimedeanVerticalChannel
            f F (h.height_schedule.height u))
        atTop
        (𝓝 (zetaCompletedExplicitFormulaArchimedeanContribution f))) :
    Tendsto
        (fun u : ℝ =>
          ∫ t in Set.Icc
              (-(F.rectangle (h.height_schedule.height u)).T)
              (F.rectangle (h.height_schedule.height u)).T,
            zetaCompletedExplicitFormulaArchimedeanRightAffineKernel f F t)
        atTop
        (𝓝 (zetaCompletedExplicitFormulaPhi f 0)) ∧
      Tendsto
        (fun u : ℝ =>
          ∫ t in Set.Icc
              (-(F.rectangle (h.height_schedule.height u)).T)
              (F.rectangle (h.height_schedule.height u)).T,
            zetaCompletedExplicitFormulaArchimedeanLeftAffineKernel f F t)
        atTop
        (𝓝
          (zetaCompletedExplicitFormulaPhi f 0 -
            zetaCompletedExplicitFormulaArchimedeanContribution f)) := by
  have hdifference :
      Tendsto
        (fun u : ℝ =>
          (∫ t in Set.Icc
              (-(F.rectangle (h.height_schedule.height u)).T)
              (F.rectangle (h.height_schedule.height u)).T,
            zetaCompletedExplicitFormulaArchimedeanRightAffineKernel f F t) -
            ∫ t in Set.Icc
              (-(F.rectangle (h.height_schedule.height u)).T)
              (F.rectangle (h.height_schedule.height u)).T,
              zetaCompletedExplicitFormulaArchimedeanLeftAffineKernel f F t)
        atTop
        (𝓝 (zetaCompletedExplicitFormulaArchimedeanContribution f)) :=
    zetaCompletedExplicitFormulaArchimedeanDifferenceAffineKernel_scheduledWindow_tendsto_of_verticalChannel
      f F h hchannel
  exact
    zetaCompletedExplicitFormulaArchimedeanAffineKernel_scheduledPair_of_right_and_difference
      f F h hright hdifference

/-- Algebraic extraction of the scheduled inverse-Gamma completion limit from
the archimedean vertical-channel limit and the scheduled correction limit.

This is the reverse assembly direction: after the archimedean channel has been
proved independently, the fixed-height identity
`archimedean = inverseGammaCompletion - correction` gives
`inverseGammaCompletion = archimedean + correction`. -/
theorem zetaCompletedExplicitFormulaScheduledInverseGammaCompletionVerticalChannel_tendsto_of_archimedean_and_scheduledCorrection
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (harch :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaArchimedeanVerticalChannel
            f F (h.height_schedule.height u))
        atTop
        (𝓝 (zetaCompletedExplicitFormulaArchimedeanContribution f)))
    (hcorrection :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaScheduledCorrectionVerticalChannel
            f F h u)
        atTop
        (𝓝 (zetaCompletedExplicitFormulaCorrectionStandardContourContribution f))) :
    Tendsto
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaScheduledInverseGammaCompletionVerticalChannel
          f F h u)
      atTop
      (𝓝
        (zetaCompletedExplicitFormulaArchimedeanContribution f +
          zetaCompletedExplicitFormulaCorrectionStandardContourContribution f)) := by
  let A : ℂ := zetaCompletedExplicitFormulaArchimedeanContribution f
  let C : ℂ := zetaCompletedExplicitFormulaCorrectionStandardContourContribution f
  have hsum :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaArchimedeanVerticalChannel
              f F (h.height_schedule.height u) +
            zetaCompletedExplicitFormulaScheduledCorrectionVerticalChannel
              f F h u)
        atTop
        (𝓝 (A + C)) :=
    harch.add hcorrection
  have hinverse_fun :
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaScheduledInverseGammaCompletionVerticalChannel
          f F h u) =
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaArchimedeanVerticalChannel
            f F (h.height_schedule.height u) +
          zetaCompletedExplicitFormulaScheduledCorrectionVerticalChannel
            f F h u) := by
    funext u
    let A_u : ℂ :=
      zetaCompletedExplicitFormulaArchimedeanVerticalChannel
        f F (h.height_schedule.height u)
    let C_u : ℂ :=
      zetaCompletedExplicitFormulaScheduledCorrectionVerticalChannel
        f F h u
    let G_u : ℂ :=
      zetaCompletedExplicitFormulaScheduledInverseGammaCompletionVerticalChannel
        f F h u
    have hdecomp : A_u = G_u - C_u :=
      zetaCompletedExplicitFormulaScheduledArchimedean_eq_inverseGammaCompletion_sub_correction
        f F h u
    change G_u = A_u + C_u
    calc
      G_u = (G_u - C_u) + C_u := by
        exact (sub_add_cancel G_u C_u).symm
      _ = A_u + C_u := by
        exact congrArg (fun z : ℂ => z + C_u) hdecomp.symm
  exact Eq.subst
    (motive := fun φ : ℝ → ℂ => Tendsto φ atTop (𝓝 (A + C)))
    hinverse_fun.symm
    hsum

/-- Archimedean channel transport after replacing the correction-channel analytic
estimate by its pole-face owner theorem.  The remaining analytic input is the
inverse-Gamma completion vertical-channel convergence and the upstream
right-one-pole decay needed by the correction channel. -/
theorem zetaCompletedExplicitFormulaArchimedeanVerticalChannel_tendsto_of_scheduledInverseGammaCompletion_and_rightOnePoleDecay
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (hinverse :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaScheduledInverseGammaCompletionVerticalChannel
            f F h u)
        atTop
        (𝓝
          (zetaCompletedExplicitFormulaArchimedeanContribution f +
            zetaCompletedExplicitFormulaCorrectionStandardContourContribution f)))
    (hone :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaCorrectionRightOnePoleVerticalIntegral
            f F (h.height_schedule.height u))
        atTop
        (𝓝 (zetaCompletedExplicitFormulaRightOnePoleCauchyProjectionValue f F.c))) :
    Tendsto
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaArchimedeanVerticalChannel
          f F (h.height_schedule.height u))
      atTop
      (𝓝 (zetaCompletedExplicitFormulaArchimedeanContribution f)) := by
  have hcorrection :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaScheduledCorrectionVerticalChannel
            f F h u)
        atTop
        (𝓝 (zetaCompletedExplicitFormulaCorrectionStandardContourContribution f)) :=
    zetaCompletedExplicitFormulaCorrectionVerticalChannel_tendsto_correctionContribution_concrete_ownerChannelTransportAnalytic
      f F h hone
  exact
    zetaCompletedExplicitFormulaArchimedeanVerticalChannel_tendsto_of_scheduledInverseGammaCompletion_and_scheduledCorrection
      f F h hinverse hcorrection

/-- Owner transport theorem: the scheduled Gamma/completion vertical channel
converges to the completed archimedean contribution after consuming the named
inverse-Gamma completion estimate and correction-channel estimate. -/
theorem zetaCompletedExplicitFormulaArchimedeanVerticalChannel_tendsto_archimedeanContribution_ownerArchimedeanTransport
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (hregular : zetaCompletedExplicitFormulaLeftAffineLineGammaRegular F)
    (hcoh : Complex.gammaBinetPrincipalLogCoherence)
    (hvalue :
      (∫ t : ℝ,
        zetaCompletedExplicitFormulaInverseGammaDifferenceAffineKernel f F t) =
        zetaCompletedExplicitFormulaArchimedeanContribution f +
          zetaCompletedExplicitFormulaCorrectionStandardContourContribution f) :
    Tendsto
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaArchimedeanVerticalChannel
          f F (h.height_schedule.height u))
      atTop
      (𝓝 (zetaCompletedExplicitFormulaArchimedeanContribution f)) := by
  have hestimates :
      Tendsto
          (fun u : ℝ =>
            zetaCompletedExplicitFormulaScheduledInverseGammaCompletionVerticalChannel
              f F h u)
          atTop
          (𝓝
            (zetaCompletedExplicitFormulaArchimedeanContribution f +
              zetaCompletedExplicitFormulaCorrectionStandardContourContribution f)) ∧
        Tendsto
          (fun u : ℝ =>
            zetaCompletedExplicitFormulaScheduledCorrectionVerticalChannel
              f F h u)
          atTop
          (𝓝 (zetaCompletedExplicitFormulaCorrectionStandardContourContribution f)) := by
    exact
      zetaCompletedExplicitFormulaScheduledArchimedeanEstimates_tendsto
        f F h hregular hcoh hvalue
  exact
    zetaCompletedExplicitFormulaArchimedeanVerticalChannel_tendsto_of_scheduledInverseGammaCompletion_and_scheduledCorrection
      f F h hestimates.1 hestimates.2

/-- Vertically regular archimedean-channel transport with Gamma regularity
supplied by the contour owner.  The remaining analytic input is the whole-line
inverse-Gamma value identity. -/
theorem zetaCompletedExplicitFormulaArchimedeanVerticalChannel_tendsto_archimedeanContribution_of_verticallyRegular_gammaBinet_integral_eq
    (f : ZetaAdmissibleFunction)
    (F : ExplicitFormulaVerticallyRegularContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F.toContourFamily)
    (hcoh : Complex.gammaBinetPrincipalLogCoherence)
    (hvalue :
      (∫ t : ℝ,
        zetaCompletedExplicitFormulaInverseGammaDifferenceAffineKernel
          f F.toContourFamily t) =
        zetaCompletedExplicitFormulaArchimedeanContribution f +
          zetaCompletedExplicitFormulaCorrectionStandardContourContribution f) :
    Tendsto
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaArchimedeanVerticalChannel
          f F.toContourFamily (h.height_schedule.height u))
      atTop
      (𝓝 (zetaCompletedExplicitFormulaArchimedeanContribution f)) := by
  have hestimates :
      Tendsto
          (fun u : ℝ =>
            zetaCompletedExplicitFormulaScheduledInverseGammaCompletionVerticalChannel
              f F.toContourFamily h u)
          atTop
          (𝓝
            (zetaCompletedExplicitFormulaArchimedeanContribution f +
              zetaCompletedExplicitFormulaCorrectionStandardContourContribution f)) ∧
        Tendsto
          (fun u : ℝ =>
            zetaCompletedExplicitFormulaScheduledCorrectionVerticalChannel
              f F.toContourFamily h u)
          atTop
          (𝓝 (zetaCompletedExplicitFormulaCorrectionStandardContourContribution f)) :=
    zetaCompletedExplicitFormulaScheduledArchimedeanEstimates_tendsto_of_verticallyRegular_gammaBinet_integral_eq
      f F h hcoh hvalue
  exact
    zetaCompletedExplicitFormulaArchimedeanVerticalChannel_tendsto_of_scheduledInverseGammaCompletion_and_scheduledCorrection
      f F.toContourFamily h hestimates.1 hestimates.2

/-- Vertically regular scheduled right-minus-left archimedean affine window
convergence in named affine-kernel normal form.

This is the affine-window projection of
`zetaCompletedExplicitFormulaArchimedeanVerticalChannel_tendsto_archimedeanContribution_of_verticallyRegular_gammaBinet_integral_eq`.
It is still a right-minus-left theorem, but the conclusion is now expressed as
the two named finite-height affine windows that the paired owner theorem must
evaluate separately. -/
theorem zetaCompletedExplicitFormulaArchimedeanAffineWindowDifference_tendsto_archimedeanContribution_of_verticallyRegular_gammaBinet_integral_eq
    (f : ZetaAdmissibleFunction)
    (F : ExplicitFormulaVerticallyRegularContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F.toContourFamily)
    (hcoh : Complex.gammaBinetPrincipalLogCoherence)
    (hvalue :
      (∫ t : ℝ,
        zetaCompletedExplicitFormulaInverseGammaDifferenceAffineKernel
          f F.toContourFamily t) =
        zetaCompletedExplicitFormulaArchimedeanContribution f +
          zetaCompletedExplicitFormulaCorrectionStandardContourContribution f) :
    Tendsto
      (fun u : ℝ =>
        (∫ t in Set.Icc
            (-(F.toContourFamily.rectangle (h.height_schedule.height u)).T)
            (F.toContourFamily.rectangle (h.height_schedule.height u)).T,
          zetaCompletedExplicitFormulaArchimedeanRightAffineKernel
            f F.toContourFamily t) -
          ∫ t in Set.Icc
            (-(F.toContourFamily.rectangle (h.height_schedule.height u)).T)
            (F.toContourFamily.rectangle (h.height_schedule.height u)).T,
            zetaCompletedExplicitFormulaArchimedeanLeftAffineKernel
              f F.toContourFamily t)
      atTop
      (𝓝 (zetaCompletedExplicitFormulaArchimedeanContribution f)) := by
  have hchannel :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaArchimedeanVerticalChannel
            f F.toContourFamily (h.height_schedule.height u))
        atTop
        (𝓝 (zetaCompletedExplicitFormulaArchimedeanContribution f)) :=
    zetaCompletedExplicitFormulaArchimedeanVerticalChannel_tendsto_archimedeanContribution_of_verticallyRegular_gammaBinet_integral_eq
      f F h hcoh hvalue
  exact
    zetaCompletedExplicitFormulaArchimedeanDifferenceAffineKernel_scheduledWindow_tendsto_of_verticalChannel
      f F.toContourFamily h hchannel

/-- Vertically regular paired scheduled affine values from the right scheduled
affine value and the inverse-Gamma difference normalization.

The inverse-Gamma normalization is used only to obtain the right-minus-left
archimedean affine-window convergence through the vertical-channel theorem.
The remaining one-sided analytic input is the right affine scheduled contour
value. -/
theorem zetaCompletedExplicitFormulaArchimedeanAffineKernel_scheduledPair_of_right_and_verticallyRegular_gammaBinet_integral_eq
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
    (hvalue :
      (∫ t : ℝ,
        zetaCompletedExplicitFormulaInverseGammaDifferenceAffineKernel
          f F.toContourFamily t) =
        zetaCompletedExplicitFormulaArchimedeanContribution f +
          zetaCompletedExplicitFormulaCorrectionStandardContourContribution f) :
    Tendsto
        (fun u : ℝ =>
          ∫ t in Set.Icc
              (-(F.toContourFamily.rectangle (h.height_schedule.height u)).T)
              (F.toContourFamily.rectangle (h.height_schedule.height u)).T,
            zetaCompletedExplicitFormulaArchimedeanRightAffineKernel
              f F.toContourFamily t)
        atTop
        (𝓝 (zetaCompletedExplicitFormulaPhi f 0)) ∧
      Tendsto
        (fun u : ℝ =>
          ∫ t in Set.Icc
              (-(F.toContourFamily.rectangle (h.height_schedule.height u)).T)
              (F.toContourFamily.rectangle (h.height_schedule.height u)).T,
            zetaCompletedExplicitFormulaArchimedeanLeftAffineKernel
              f F.toContourFamily t)
        atTop
        (𝓝
          (zetaCompletedExplicitFormulaPhi f 0 -
            zetaCompletedExplicitFormulaArchimedeanContribution f)) := by
  have hdifference :
      Tendsto
        (fun u : ℝ =>
          (∫ t in Set.Icc
              (-(F.toContourFamily.rectangle (h.height_schedule.height u)).T)
              (F.toContourFamily.rectangle (h.height_schedule.height u)).T,
            zetaCompletedExplicitFormulaArchimedeanRightAffineKernel
              f F.toContourFamily t) -
            ∫ t in Set.Icc
              (-(F.toContourFamily.rectangle (h.height_schedule.height u)).T)
              (F.toContourFamily.rectangle (h.height_schedule.height u)).T,
              zetaCompletedExplicitFormulaArchimedeanLeftAffineKernel
                f F.toContourFamily t)
        atTop
        (𝓝 (zetaCompletedExplicitFormulaArchimedeanContribution f)) :=
    zetaCompletedExplicitFormulaArchimedeanAffineWindowDifference_tendsto_archimedeanContribution_of_verticallyRegular_gammaBinet_integral_eq
      f F h hcoh hvalue
  exact
    zetaCompletedExplicitFormulaArchimedeanAffineKernel_scheduledPair_of_right_and_difference
      f F.toContourFamily h hright hdifference

/-- Owner transport-remainder form of the archimedean Gamma/completion vertical
channel estimate.  The analytic content is the channel convergence theorem
above; this theorem only subtracts the boundary contribution. -/
theorem zetaCompletedExplicitFormulaArchimedeanVerticalChannelTransportRemainder_tendsto_zero_ownerArchimedeanTransport
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (hregular : zetaCompletedExplicitFormulaLeftAffineLineGammaRegular F)
    (hcoh : Complex.gammaBinetPrincipalLogCoherence)
    (hvalue :
      (∫ t : ℝ,
        zetaCompletedExplicitFormulaInverseGammaDifferenceAffineKernel f F t) =
        zetaCompletedExplicitFormulaArchimedeanContribution f +
          zetaCompletedExplicitFormulaCorrectionStandardContourContribution f) :
    Tendsto
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaArchimedeanVerticalChannelTransportRemainder
          f F (h.height_schedule.height u))
      atTop
      (𝓝 0) := by
  exact
    zetaCompletedExplicitFormulaArchimedeanVerticalChannelTransportRemainder_tendsto_zero_of_channel_tendsto_archimedeanContribution
      f F h
      (zetaCompletedExplicitFormulaArchimedeanVerticalChannel_tendsto_archimedeanContribution_ownerArchimedeanTransport
        f F h hregular hcoh hvalue)

/-- Vertically regular transport-remainder form of the archimedean channel
estimate.  The whole-line inverse-Gamma value identity remains explicit. -/
theorem zetaCompletedExplicitFormulaArchimedeanVerticalChannelTransportRemainder_tendsto_zero_of_verticallyRegular_gammaBinet_integral_eq
    (f : ZetaAdmissibleFunction)
    (F : ExplicitFormulaVerticallyRegularContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F.toContourFamily)
    (hcoh : Complex.gammaBinetPrincipalLogCoherence)
    (hvalue :
      (∫ t : ℝ,
        zetaCompletedExplicitFormulaInverseGammaDifferenceAffineKernel
          f F.toContourFamily t) =
        zetaCompletedExplicitFormulaArchimedeanContribution f +
          zetaCompletedExplicitFormulaCorrectionStandardContourContribution f) :
    Tendsto
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaArchimedeanVerticalChannelTransportRemainder
          f F.toContourFamily (h.height_schedule.height u))
      atTop
      (𝓝 0) := by
  exact
    zetaCompletedExplicitFormulaArchimedeanVerticalChannelTransportRemainder_tendsto_zero_of_channel_tendsto_archimedeanContribution
      f F.toContourFamily h
      (zetaCompletedExplicitFormulaArchimedeanVerticalChannel_tendsto_archimedeanContribution_of_verticallyRegular_gammaBinet_integral_eq
        f F h hcoh hvalue)

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
