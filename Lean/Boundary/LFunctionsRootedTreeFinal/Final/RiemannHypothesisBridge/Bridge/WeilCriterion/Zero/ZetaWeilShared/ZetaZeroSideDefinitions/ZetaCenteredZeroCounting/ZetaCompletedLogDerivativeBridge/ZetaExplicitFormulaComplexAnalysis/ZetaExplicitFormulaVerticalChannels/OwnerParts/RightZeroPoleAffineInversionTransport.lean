import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.PoleKernelVerticalInversion
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.ScheduledKernelLimitTransport
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.SymmetricIntegralExhaustion
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.ZeroPoleAffineKernelIntegrability

/-!
# Right zero-pole affine inversion transport

This file owns the non-analytic transport around the isolated right `s = 0`
pole kernel.  The Cauchy/Laplace value itself remains a separate owner leaf.
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

/-- Owner-level affine-kernel normal form for the right zero-pole vertical
inversion integrand. -/
theorem zetaCompletedExplicitFormulaCorrectionRightZeroPoleVerticalInversionIntegrand_eq_affineKernel_ownerTransport
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T t : ℝ) :
    zetaCompletedExplicitFormulaCorrectionRightZeroPoleVerticalInversionIntegrand
        f F T t =
      zetaCompletedExplicitFormulaCorrectionRightZeroPoleAffineKernel f F t := by
  have hscheduled :
      zetaCompletedExplicitFormulaCorrectionRightZeroPoleVerticalInversionIntegrand
          f F T t =
        (-1 / ((F.c : ℂ) + t * Complex.I)) *
          zetaCompletedExplicitFormulaPhi f
            (((F.c : ℂ) - (1 / 2 : ℂ)) + t * Complex.I) :=
    zetaCompletedExplicitFormulaCorrectionRightZeroPoleVerticalInversionIntegrand_eq_affineLine
      f F T t
  have haffine :
      zetaCompletedExplicitFormulaCorrectionRightZeroPoleAffineKernel f F t =
        (-1 / ((F.c : ℂ) + t * Complex.I)) *
          zetaCompletedExplicitFormulaPhi f
            (((F.c : ℂ) - (1 / 2 : ℂ)) + t * Complex.I) := by
    let R : ℂ := zetaCompletedExplicitFormulaRightAffineLine F t
    let C : ℂ := zetaCompletedExplicitFormulaRightCenteredAffineLine F t
    have hR : R = (F.c : ℂ) + t * Complex.I :=
      zetaCompletedExplicitFormulaRightAffineLine_eq F t
    have hC : C = ((F.c : ℂ) - (1 / 2 : ℂ)) + t * Complex.I :=
      zetaCompletedExplicitFormulaRightCenteredAffineLine_eq F t
    calc
      zetaCompletedExplicitFormulaCorrectionRightZeroPoleAffineKernel f F t =
          (-1 / R) * zetaCompletedExplicitFormulaPhi f C := by
        exact Eq.refl _
      _ =
          (-1 / ((F.c : ℂ) + t * Complex.I)) *
            zetaCompletedExplicitFormulaPhi f C := by
        exact
          congrArg
            (fun z : ℂ => (-1 / z) * zetaCompletedExplicitFormulaPhi f C)
            hR
      _ =
          (-1 / ((F.c : ℂ) + t * Complex.I)) *
            zetaCompletedExplicitFormulaPhi f
              (((F.c : ℂ) - (1 / 2 : ℂ)) + t * Complex.I) := by
        exact
          congrArg
            (fun z : ℂ =>
              (-1 / ((F.c : ℂ) + t * Complex.I)) *
                zetaCompletedExplicitFormulaPhi f z)
            hC
  exact Eq.trans hscheduled haffine.symm

/-- Scheduled right zero-pole vertical inversion as the named affine kernel
integral. -/
theorem zetaCompletedExplicitFormulaCorrectionRightZeroPoleScheduledVerticalInversion_eq_affineKernelIntegral_ownerTransport
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    zetaCompletedExplicitFormulaCorrectionRightZeroPoleScheduledVerticalInversion
        f F h u =
      ∫ t in
          Set.Icc
            (-(F.rectangle (h.height_schedule.height u)).T)
            (F.rectangle (h.height_schedule.height u)).T,
        zetaCompletedExplicitFormulaCorrectionRightZeroPoleAffineKernel f F t := by
  have hfun :
      (fun t : ℝ =>
        zetaCompletedExplicitFormulaCorrectionRightZeroPoleVerticalInversionIntegrand
          f F (h.height_schedule.height u) t) =
      (fun t : ℝ =>
        zetaCompletedExplicitFormulaCorrectionRightZeroPoleAffineKernel f F t) := by
    funext t
    exact
      zetaCompletedExplicitFormulaCorrectionRightZeroPoleVerticalInversionIntegrand_eq_affineKernel_ownerTransport
        f F (h.height_schedule.height u) t
  exact
    congrArg
      (fun φ : ℝ → ℂ =>
        ∫ t in
            Set.Icc
              (-(F.rectangle (h.height_schedule.height u)).T)
              (F.rectangle (h.height_schedule.height u)).T,
          φ t)
      hfun

/-- Integrability of the isolated right zero-pole affine inversion kernel. -/
theorem zetaCompletedExplicitFormulaCorrectionRightZeroPoleAffineKernel_integrable_ownerTransport
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) :
    Integrable
      (zetaCompletedExplicitFormulaCorrectionRightZeroPoleAffineKernel f F)
      (volume : Measure ℝ) :=
  zetaCompletedExplicitFormulaCorrectionRightZeroPoleAffineKernel_integrable_ownerBounds
    f F h

/-- Scheduled-window convergence of the right zero-pole affine kernel to its
whole-line integral. -/
theorem zetaCompletedExplicitFormulaCorrectionRightZeroPoleAffineKernelIntegral_tendsto_integral_ownerTransport
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) :
    Tendsto
      (fun u : ℝ =>
        ∫ t in Set.Icc
            (-(F.rectangle (h.height_schedule.height u)).T)
            (F.rectangle (h.height_schedule.height u)).T,
          zetaCompletedExplicitFormulaCorrectionRightZeroPoleAffineKernel f F t)
      atTop
      (𝓝 (∫ t : ℝ,
        zetaCompletedExplicitFormulaCorrectionRightZeroPoleAffineKernel f F t)) := by
  let K : ℝ → ℂ := fun T : ℝ =>
    ∫ t in Set.Icc
        (-(F.rectangle T).T)
        (F.rectangle T).T,
      zetaCompletedExplicitFormulaCorrectionRightZeroPoleAffineKernel f F t
  have hsymmetric :
      Tendsto
        (fun T : ℝ =>
          ∫ t in Set.Icc (-T) T,
            zetaCompletedExplicitFormulaCorrectionRightZeroPoleAffineKernel f F t)
        atTop
        (𝓝 (∫ t : ℝ,
          zetaCompletedExplicitFormulaCorrectionRightZeroPoleAffineKernel f F t)) :=
    explicitFormulaSymmetricIntervalIntegral_tendsto_integral
      (zetaCompletedExplicitFormulaCorrectionRightZeroPoleAffineKernel f F)
      (zetaCompletedExplicitFormulaCorrectionRightZeroPoleAffineKernel_integrable_ownerTransport
        f F h)
  have hkernel :
      Tendsto K atTop
        (𝓝 (∫ t : ℝ,
          zetaCompletedExplicitFormulaCorrectionRightZeroPoleAffineKernel f F t)) :=
    explicitFormulaRectangleWindowIntegral_tendsto_of_symmetric
      F
      (zetaCompletedExplicitFormulaCorrectionRightZeroPoleAffineKernel f F)
      (∫ t : ℝ,
        zetaCompletedExplicitFormulaCorrectionRightZeroPoleAffineKernel f F t)
      hsymmetric
  exact
    explicitFormulaScheduledScalar_tendsto_of_unscheduled
      K
      h.height_schedule.height
      (∫ t : ℝ,
        zetaCompletedExplicitFormulaCorrectionRightZeroPoleAffineKernel f F t)
      hkernel
      h.height_schedule.cofinal

/-- Scheduled right zero-pole inversion follows from the whole-line
Cauchy/Laplace affine-kernel value. -/
theorem zetaCompletedExplicitFormulaCorrectionRightZeroPoleScheduledVerticalInversion_tendsto_value_of_affineKernel_integral_eq_ownerTransport
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (hvalue :
      (∫ t : ℝ,
        zetaCompletedExplicitFormulaCorrectionRightZeroPoleAffineKernel f F t) =
        zetaCompletedExplicitFormulaCorrectionRightZeroPoleVerticalInversionValue f) :
    Tendsto
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaCorrectionRightZeroPoleScheduledVerticalInversion
          f F h u)
      atTop
      (𝓝 (zetaCompletedExplicitFormulaCorrectionRightZeroPoleVerticalInversionValue f)) := by
  let K : ℝ → ℂ := fun u : ℝ =>
    ∫ t in Set.Icc
        (-(F.rectangle (h.height_schedule.height u)).T)
        (F.rectangle (h.height_schedule.height u)).T,
      zetaCompletedExplicitFormulaCorrectionRightZeroPoleAffineKernel f F t
  have hintegral :
      Tendsto K atTop
        (𝓝 (∫ t : ℝ,
          zetaCompletedExplicitFormulaCorrectionRightZeroPoleAffineKernel f F t)) :=
    zetaCompletedExplicitFormulaCorrectionRightZeroPoleAffineKernelIntegral_tendsto_integral_ownerTransport
      f F h
  have htarget :
      Tendsto K atTop
        (𝓝 (zetaCompletedExplicitFormulaCorrectionRightZeroPoleVerticalInversionValue f)) :=
    Eq.subst
      (motive := fun z : ℂ => Tendsto K atTop (𝓝 z))
      hvalue
      hintegral
  exact
    explicitFormulaScheduledScalar_tendsto_of_forall_eq
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaCorrectionRightZeroPoleScheduledVerticalInversion
          f F h u)
      K
      (zetaCompletedExplicitFormulaCorrectionRightZeroPoleVerticalInversionValue f)
      htarget
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaCorrectionRightZeroPoleScheduledVerticalInversion_eq_affineKernelIntegral_ownerTransport
          f F h u)

/-- The whole-line isolated right zero-pole affine-kernel value follows from an
independent scheduled vertical-inversion value theorem.

This is the non-circular uniqueness step: symmetric exhaustion identifies the
limit of the scheduled affine-kernel windows with the whole-line integral, while
the analytic Cauchy/Laplace proof supplies the scheduled value limit. -/
theorem zetaCompletedExplicitFormulaCorrectionRightZeroPoleAffineKernel_integral_eq_value_of_scheduledVerticalInversion_tendsto_value_ownerTransport
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (hscheduled :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaCorrectionRightZeroPoleScheduledVerticalInversion
            f F h u)
        atTop
        (𝓝 (zetaCompletedExplicitFormulaCorrectionRightZeroPoleVerticalInversionValue f))) :
    (∫ t : ℝ,
      zetaCompletedExplicitFormulaCorrectionRightZeroPoleAffineKernel f F t) =
      zetaCompletedExplicitFormulaCorrectionRightZeroPoleVerticalInversionValue f := by
  let K : ℝ → ℂ := fun u : ℝ =>
    ∫ t in Set.Icc
        (-(F.rectangle (h.height_schedule.height u)).T)
        (F.rectangle (h.height_schedule.height u)).T,
      zetaCompletedExplicitFormulaCorrectionRightZeroPoleAffineKernel f F t
  have hK_integral :
      Tendsto K atTop
        (𝓝
          (∫ t : ℝ,
            zetaCompletedExplicitFormulaCorrectionRightZeroPoleAffineKernel f F t)) :=
    zetaCompletedExplicitFormulaCorrectionRightZeroPoleAffineKernelIntegral_tendsto_integral_ownerTransport
      f F h
  have hpoint :
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaCorrectionRightZeroPoleScheduledVerticalInversion
          f F h u) =
      K := by
    funext u
    exact
      zetaCompletedExplicitFormulaCorrectionRightZeroPoleScheduledVerticalInversion_eq_affineKernelIntegral_ownerTransport
        f F h u
  have hK_value :
      Tendsto K atTop
        (𝓝 (zetaCompletedExplicitFormulaCorrectionRightZeroPoleVerticalInversionValue f)) :=
    Eq.subst
      (motive := fun ψ : ℝ → ℂ =>
        Tendsto ψ atTop
          (𝓝 (zetaCompletedExplicitFormulaCorrectionRightZeroPoleVerticalInversionValue f)))
      hpoint
      hscheduled
  exact
    explicitFormulaScheduledScalar_integral_eq_of_tendsto_integral_and_value
      K
      (∫ t : ℝ,
        zetaCompletedExplicitFormulaCorrectionRightZeroPoleAffineKernel f F t)
      (zetaCompletedExplicitFormulaCorrectionRightZeroPoleVerticalInversionValue f)
      hK_integral
      hK_value

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
