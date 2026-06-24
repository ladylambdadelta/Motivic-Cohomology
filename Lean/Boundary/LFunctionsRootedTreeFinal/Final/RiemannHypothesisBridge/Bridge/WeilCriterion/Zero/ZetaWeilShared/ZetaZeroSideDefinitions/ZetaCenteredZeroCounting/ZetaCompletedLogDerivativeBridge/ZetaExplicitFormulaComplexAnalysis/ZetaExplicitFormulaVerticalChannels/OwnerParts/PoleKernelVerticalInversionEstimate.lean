import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.PoleKernelVerticalInversion
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.AffineKernelMajorantPackage
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.RightZeroPoleVerticalInversionLeaf
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.ScheduledKernelLimitTransport
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.SymmetricIntegralExhaustion
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.ZeroPoleAffineKernelBounds

/-!
# Pole-kernel vertical inversion estimate

This file owns the analytic vertical-line inversion limit for the isolated
right `s = 0` pole kernel.  The transport file only changes names from this
scheduled inversion integral back to the right zero-pole vertical channel.
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

/-- The named right zero-pole affine kernel is the affine-line normal form of
the scheduled vertical-inversion integrand. -/
theorem zetaCompletedExplicitFormulaCorrectionRightZeroPoleAffineKernel_eq_affineLine
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (t : ℝ) :
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

/-- The scheduled right zero-pole vertical-inversion integrand is the named
right zero-pole affine kernel. -/
theorem zetaCompletedExplicitFormulaCorrectionRightZeroPoleVerticalInversionIntegrand_eq_affineKernel
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
            (((F.c : ℂ) - (1 / 2 : ℂ)) + t * Complex.I) :=
    zetaCompletedExplicitFormulaCorrectionRightZeroPoleAffineKernel_eq_affineLine
      f F t
  exact Eq.trans hscheduled haffine.symm

/-- Interval-integral transport from the scheduled right zero-pole integrand to
the named affine kernel. -/
theorem zetaCompletedExplicitFormulaCorrectionRightZeroPoleVerticalInversionIntegrand_intervalIntegral_eq_affineKernel
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T a b : ℝ) :
    (∫ t in Set.Icc a b,
      zetaCompletedExplicitFormulaCorrectionRightZeroPoleVerticalInversionIntegrand
        f F T t) =
      ∫ t in Set.Icc a b,
        zetaCompletedExplicitFormulaCorrectionRightZeroPoleAffineKernel f F t := by
  have hfun :
      (fun t : ℝ =>
        zetaCompletedExplicitFormulaCorrectionRightZeroPoleVerticalInversionIntegrand
          f F T t) =
      (fun t : ℝ =>
        zetaCompletedExplicitFormulaCorrectionRightZeroPoleAffineKernel f F t) := by
    funext t
    exact
      zetaCompletedExplicitFormulaCorrectionRightZeroPoleVerticalInversionIntegrand_eq_affineKernel
        f F T t
  exact
    congrArg
      (fun φ : ℝ → ℂ => ∫ t in Set.Icc a b, φ t)
      hfun

/-- Scheduled right zero-pole vertical inversion in affine-line normal form. -/
theorem zetaCompletedExplicitFormulaCorrectionRightZeroPoleScheduledVerticalInversion_eq_affineLineIntegral
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    zetaCompletedExplicitFormulaCorrectionRightZeroPoleScheduledVerticalInversion
        f F h u =
      ∫ t in
          Set.Icc
            (-(F.rectangle (h.height_schedule.height u)).T)
            (F.rectangle (h.height_schedule.height u)).T,
        (-1 / ((F.c : ℂ) + t * Complex.I)) *
          zetaCompletedExplicitFormulaPhi f
            (((F.c : ℂ) - (1 / 2 : ℂ)) + t * Complex.I) := by
  have hfun :
      (fun t : ℝ =>
        zetaCompletedExplicitFormulaCorrectionRightZeroPoleVerticalInversionIntegrand
          f F (h.height_schedule.height u) t) =
      (fun t : ℝ =>
        (-1 / ((F.c : ℂ) + t * Complex.I)) *
          zetaCompletedExplicitFormulaPhi f
            (((F.c : ℂ) - (1 / 2 : ℂ)) + t * Complex.I)) := by
    funext t
    exact
      zetaCompletedExplicitFormulaCorrectionRightZeroPoleVerticalInversionIntegrand_eq_affineLine
        f F (h.height_schedule.height u) t
  exact congrArg
    (fun φ : ℝ → ℂ =>
      ∫ t in
          Set.Icc
            (-(F.rectangle (h.height_schedule.height u)).T)
            (F.rectangle (h.height_schedule.height u)).T,
        φ t)
    hfun

/-- Scheduled right zero-pole vertical inversion as the named affine kernel
integral. -/
theorem zetaCompletedExplicitFormulaCorrectionRightZeroPoleScheduledVerticalInversion_eq_affineKernelIntegral
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    zetaCompletedExplicitFormulaCorrectionRightZeroPoleScheduledVerticalInversion
        f F h u =
      ∫ t in
          Set.Icc
            (-(F.rectangle (h.height_schedule.height u)).T)
            (F.rectangle (h.height_schedule.height u)).T,
        zetaCompletedExplicitFormulaCorrectionRightZeroPoleAffineKernel f F t :=
  zetaCompletedExplicitFormulaCorrectionRightZeroPoleVerticalInversionIntegrand_intervalIntegral_eq_affineKernel
    f F
    (h.height_schedule.height u)
    (-(F.rectangle (h.height_schedule.height u)).T)
    ((F.rectangle (h.height_schedule.height u)).T)

/-- Bundled majorant package for the isolated right `s = 0` pole affine inversion
kernel.  Analytically this is the Cauchy kernel bound on the fixed right line
combined with rapid decay of `Φ_f`. -/
theorem zetaCompletedExplicitFormulaCorrectionRightZeroPoleAffineKernel_majorantPackage
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) :
    ExplicitFormulaAffineKernelMajorantPackage
      (zetaCompletedExplicitFormulaCorrectionRightZeroPoleAffineKernel f F) := by
  exact
    { majorant :=
        fun t : ℝ =>
          zetaCompletedExplicitFormulaCorrectionRightZeroPoleAffineKernelMajorant
            f F h 2 t
      integrable_majorant :=
        zetaCompletedExplicitFormulaCorrectionRightZeroPoleAffineKernelMajorant_two_integrable
          f F h
      stronglyMeasurable_kernel :=
        zetaCompletedExplicitFormulaCorrectionRightZeroPoleAffineKernel_aestronglyMeasurable
          f F h
      norm_le_majorant :=
        Filter.Eventually.of_forall
          (fun t : ℝ =>
            zetaCompletedExplicitFormulaCorrectionRightZeroPoleAffineKernel_norm_le_majorant
              f F h 2 t) }

/-- Existential majorant package for the isolated right `s = 0` pole affine
inversion kernel. -/
theorem zetaCompletedExplicitFormulaCorrectionRightZeroPoleAffineKernel_integrableMajorant
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) :
    ∃ majorant : ℝ → ℝ,
      Integrable majorant (volume : Measure ℝ) ∧
        AEStronglyMeasurable
          (zetaCompletedExplicitFormulaCorrectionRightZeroPoleAffineKernel f F)
          (volume : Measure ℝ) ∧
        ∀ᵐ t ∂(volume : Measure ℝ),
          ‖zetaCompletedExplicitFormulaCorrectionRightZeroPoleAffineKernel f F t‖
            ≤ majorant t :=
  (zetaCompletedExplicitFormulaCorrectionRightZeroPoleAffineKernel_majorantPackage
    f F h).exists_majorant

/-- Integrability of the isolated right `s = 0` pole affine inversion kernel. -/
theorem zetaCompletedExplicitFormulaCorrectionRightZeroPoleAffineKernel_integrable
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) :
    Integrable
      (zetaCompletedExplicitFormulaCorrectionRightZeroPoleAffineKernel f F)
      (volume : Measure ℝ) :=
  (zetaCompletedExplicitFormulaCorrectionRightZeroPoleAffineKernel_majorantPackage
    f F h).integrable

/-- Symmetric-window convergence of the isolated right `s = 0` pole affine
kernel to its actual whole-line integral.  This is the measure-theoretic
exhaustion result separated from the later Cauchy/Laplace inversion value
identification. -/
theorem zetaCompletedExplicitFormulaCorrectionRightZeroPoleAffineKernelIntegral_tendsto_integral_symmetric
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) :
    Tendsto
      (fun T : ℝ =>
        ∫ t in Set.Icc (-T) T,
          zetaCompletedExplicitFormulaCorrectionRightZeroPoleAffineKernel f F t)
      atTop
      (𝓝 (∫ t : ℝ,
        zetaCompletedExplicitFormulaCorrectionRightZeroPoleAffineKernel f F t)) := by
  exact
    explicitFormulaSymmetricIntervalIntegral_tendsto_integral
      (zetaCompletedExplicitFormulaCorrectionRightZeroPoleAffineKernel f F)
      (zetaCompletedExplicitFormulaCorrectionRightZeroPoleAffineKernel_integrable
        f F h)

/-- Rectangle-window convergence of the isolated right `s = 0` pole affine
kernel to its actual whole-line integral. -/
theorem zetaCompletedExplicitFormulaCorrectionRightZeroPoleAffineKernelIntegral_tendsto_integral_unscheduled
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) :
    Tendsto
      (fun T : ℝ =>
        ∫ t in Set.Icc
            (-(F.rectangle T).T)
            (F.rectangle T).T,
          zetaCompletedExplicitFormulaCorrectionRightZeroPoleAffineKernel f F t)
      atTop
      (𝓝 (∫ t : ℝ,
        zetaCompletedExplicitFormulaCorrectionRightZeroPoleAffineKernel f F t)) := by
  exact
    explicitFormulaRectangleWindowIntegral_tendsto_of_symmetric
      F
      (zetaCompletedExplicitFormulaCorrectionRightZeroPoleAffineKernel f F)
      (∫ t : ℝ,
        zetaCompletedExplicitFormulaCorrectionRightZeroPoleAffineKernel f F t)
      (zetaCompletedExplicitFormulaCorrectionRightZeroPoleAffineKernelIntegral_tendsto_integral_symmetric
        f F h)

/-- Scheduled-window convergence of the isolated right `s = 0` pole affine
kernel to its actual whole-line integral. -/
theorem zetaCompletedExplicitFormulaCorrectionRightZeroPoleAffineKernelIntegral_tendsto_integral
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
  have hkernel :
      Tendsto K atTop
        (𝓝 (∫ t : ℝ,
          zetaCompletedExplicitFormulaCorrectionRightZeroPoleAffineKernel f F t)) :=
    zetaCompletedExplicitFormulaCorrectionRightZeroPoleAffineKernelIntegral_tendsto_integral_unscheduled
      f F h
  exact
    explicitFormulaScheduledScalar_tendsto_of_unscheduled
      K
      h.height_schedule.height
      (∫ t : ℝ,
        zetaCompletedExplicitFormulaCorrectionRightZeroPoleAffineKernel f F t)
      hkernel
      h.height_schedule.cofinal

/-- Symmetric-window vertical-inversion convergence from a separately proved
Cauchy/Laplace value theorem for the isolated right `s = 0` pole kernel. -/
theorem zetaCompletedExplicitFormulaCorrectionRightZeroPoleAffineKernelIntegral_tendsto_value_symmetric_of_integral_eq
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (hvalue :
      (∫ t : ℝ,
        zetaCompletedExplicitFormulaCorrectionRightZeroPoleAffineKernel f F t) =
        zetaCompletedExplicitFormulaCorrectionRightZeroPoleVerticalInversionValue f) :
    Tendsto
      (fun T : ℝ =>
        ∫ t in Set.Icc (-T) T,
          zetaCompletedExplicitFormulaCorrectionRightZeroPoleAffineKernel f F t)
      atTop
      (𝓝 (zetaCompletedExplicitFormulaCorrectionRightZeroPoleVerticalInversionValue f)) := by
  exact
    explicitFormulaSymmetricIntervalIntegral_tendsto_value
      (zetaCompletedExplicitFormulaCorrectionRightZeroPoleAffineKernel f F)
      (zetaCompletedExplicitFormulaCorrectionRightZeroPoleVerticalInversionValue f)
      (zetaCompletedExplicitFormulaCorrectionRightZeroPoleAffineKernel_integrable
        f F h)
      hvalue

/-- Rectangle-window vertical-inversion convergence from a separately proved
Cauchy/Laplace value theorem for the isolated right `s = 0` pole kernel. -/
theorem zetaCompletedExplicitFormulaCorrectionRightZeroPoleAffineKernelIntegral_tendsto_value_unscheduled_of_integral_eq
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (hvalue :
      (∫ t : ℝ,
        zetaCompletedExplicitFormulaCorrectionRightZeroPoleAffineKernel f F t) =
        zetaCompletedExplicitFormulaCorrectionRightZeroPoleVerticalInversionValue f) :
    Tendsto
      (fun T : ℝ =>
        ∫ t in Set.Icc
            (-(F.rectangle T).T)
            (F.rectangle T).T,
          zetaCompletedExplicitFormulaCorrectionRightZeroPoleAffineKernel f F t)
      atTop
      (𝓝 (zetaCompletedExplicitFormulaCorrectionRightZeroPoleVerticalInversionValue f)) := by
  exact
    explicitFormulaRectangleWindowIntegral_tendsto_of_symmetric
      F
      (zetaCompletedExplicitFormulaCorrectionRightZeroPoleAffineKernel f F)
      (zetaCompletedExplicitFormulaCorrectionRightZeroPoleVerticalInversionValue f)
      (zetaCompletedExplicitFormulaCorrectionRightZeroPoleAffineKernelIntegral_tendsto_value_symmetric_of_integral_eq
        f F h hvalue)

/-- Scheduled-window vertical-inversion convergence from a separately proved
Cauchy/Laplace value theorem for the isolated right `s = 0` pole kernel. -/
theorem zetaCompletedExplicitFormulaCorrectionRightZeroPoleAffineKernelIntegral_tendsto_value_of_integral_eq
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (hvalue :
      (∫ t : ℝ,
        zetaCompletedExplicitFormulaCorrectionRightZeroPoleAffineKernel f F t) =
        zetaCompletedExplicitFormulaCorrectionRightZeroPoleVerticalInversionValue f) :
    Tendsto
      (fun u : ℝ =>
        ∫ t in Set.Icc
            (-(F.rectangle (h.height_schedule.height u)).T)
            (F.rectangle (h.height_schedule.height u)).T,
          zetaCompletedExplicitFormulaCorrectionRightZeroPoleAffineKernel f F t)
      atTop
      (𝓝 (zetaCompletedExplicitFormulaCorrectionRightZeroPoleVerticalInversionValue f)) := by
  let K : ℝ → ℂ := fun T : ℝ =>
    ∫ t in Set.Icc
        (-(F.rectangle T).T)
        (F.rectangle T).T,
      zetaCompletedExplicitFormulaCorrectionRightZeroPoleAffineKernel f F t
  have hkernel :
      Tendsto K atTop
        (𝓝 (zetaCompletedExplicitFormulaCorrectionRightZeroPoleVerticalInversionValue f)) :=
    zetaCompletedExplicitFormulaCorrectionRightZeroPoleAffineKernelIntegral_tendsto_value_unscheduled_of_integral_eq
      f F h hvalue
  exact
    explicitFormulaScheduledScalar_tendsto_of_unscheduled
      K
      h.height_schedule.height
      (zetaCompletedExplicitFormulaCorrectionRightZeroPoleVerticalInversionValue f)
      hkernel
      h.height_schedule.cofinal

/-- The whole-line isolated right zero-pole affine-kernel value follows from an
independent scheduled vertical-inversion value theorem.  This is the
non-circular uniqueness step: exhaustion gives the limit as the whole-line
integral, while the Cauchy/Laplace proof supplies the scheduled value limit. -/
theorem zetaCompletedExplicitFormulaCorrectionRightZeroPoleAffineKernel_integral_eq_value_of_scheduledVerticalInversion_tendsto_value
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
    zetaCompletedExplicitFormulaCorrectionRightZeroPoleAffineKernelIntegral_tendsto_integral
      f F h
  have hpoint :
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaCorrectionRightZeroPoleScheduledVerticalInversion
          f F h u) =
      K := by
    funext u
    exact
      zetaCompletedExplicitFormulaCorrectionRightZeroPoleScheduledVerticalInversion_eq_affineKernelIntegral
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

/-- Direct scheduled Cauchy/Laplace inversion for the isolated right `s = 0`
pole kernel.

This is the analytic leaf under the whole-line affine-kernel value theorem.
It is stated at the scheduled vertical-inversion owner level because the proof
is a contour/Laplace inversion argument for the scheduled pole face; the
whole-line integral identity below is only the uniqueness-of-limits transport. -/
theorem zetaCompletedExplicitFormulaCorrectionRightZeroPoleScheduledVerticalInversion_tendsto_value_direct
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) :
    Tendsto
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaCorrectionRightZeroPoleScheduledVerticalInversion
          f F h u)
      atTop
      (𝓝 (zetaCompletedExplicitFormulaCorrectionRightZeroPoleVerticalInversionValue f)) := by
  exact
    zetaCompletedExplicitFormulaCorrectionRightZeroPoleScheduledVerticalInversion_tendsto_value_ownerInversion
      f F h

/-- Whole-line Cauchy/Laplace inversion value for the isolated right `s = 0`
pole affine kernel. -/
theorem zetaCompletedExplicitFormulaCorrectionRightZeroPoleAffineKernel_integral_eq_value
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) :
    (∫ t : ℝ,
      zetaCompletedExplicitFormulaCorrectionRightZeroPoleAffineKernel f F t) =
      zetaCompletedExplicitFormulaCorrectionRightZeroPoleVerticalInversionValue f := by
  exact
    zetaCompletedExplicitFormulaCorrectionRightZeroPoleAffineKernel_integral_eq_value_ownerInversion
      f F h

/-- Analytic vertical-inversion estimate for the isolated right `s = 0` pole
kernel, transported from the owner Cauchy/Laplace inversion leaf. -/
theorem zetaCompletedExplicitFormulaCorrectionRightZeroPoleScheduledVerticalInversion_tendsto_value
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) :
    Tendsto
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaCorrectionRightZeroPoleScheduledVerticalInversion
          f F h u)
      atTop
      (𝓝 (zetaCompletedExplicitFormulaCorrectionRightZeroPoleVerticalInversionValue f)) := by
  exact
    zetaCompletedExplicitFormulaCorrectionRightZeroPoleScheduledVerticalInversion_tendsto_value_ownerInversion
      f F h

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
