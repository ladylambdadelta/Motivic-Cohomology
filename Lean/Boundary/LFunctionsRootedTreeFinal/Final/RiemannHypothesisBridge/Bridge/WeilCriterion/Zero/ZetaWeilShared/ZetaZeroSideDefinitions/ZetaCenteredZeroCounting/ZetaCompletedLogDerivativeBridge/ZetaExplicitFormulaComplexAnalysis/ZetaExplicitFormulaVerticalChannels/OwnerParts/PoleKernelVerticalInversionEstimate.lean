import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.PoleKernelVerticalInversion
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.AffineKernelMajorantPackage
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.RightZeroPoleCauchyAssembly
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.ZeroPoleLeftOffPoleDecay
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.ScheduledKernelLimitTransport
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.SymmetricIntegralExhaustion
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.ZeroPoleAffineKernelBounds
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.ZeroPoleSquarePuncturedProjectBridge
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.CorrectionPoleResidues

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
def zetaCompletedExplicitFormulaCorrectionRightZeroPoleAffineKernel_majorantPackage
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

/-- Source tangent-boundary limit for the zero-pole rectangle. -/
theorem zetaCompletedExplicitFormulaCorrectionZeroPoleTangentRectangleBoundaryIntegral_tendsto_localTangentResidueValue_poleKernelSource
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) :
    Tendsto
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaCorrectionZeroPoleTangentRectangleBoundaryIntegral
          f F (h.height_schedule.height u))
      atTop
      (𝓝
        (zetaCompletedExplicitFormulaCorrectionZeroPoleLocalTangentResidueValue f)) := by
  let S : ℝ → ℂ := fun u : ℝ =>
    zetaCompletedExplicitFormulaCorrectionZeroPoleStandardRectangleBoundaryIntegral
      f F (h.height_schedule.height u)
  let D : ℝ → ℂ := fun u : ℝ =>
    zetaCompletedExplicitFormulaCorrectionZeroPoleTangentOrientationDefect
      f F (h.height_schedule.height u)
  let C : ℝ → ℂ := fun u : ℝ =>
    zetaCompletedExplicitFormulaCorrectionZeroPoleTangentRectangleBoundaryIntegral
      f F (h.height_schedule.height u)
  have hstandard_event :
      S =ᶠ[atTop]
        fun _u : ℝ =>
          zetaCompletedExplicitFormulaCorrectionZeroPoleLocalTangentResidueValue f :=
    h.height_schedule.eventually_height_pos.mono
      (fun u hu =>
        zetaCompletedExplicitFormulaCorrectionZeroPoleStandardRectangleBoundaryIntegral_eq_localTangentResidueValue_of_pos_height
          f F h hu)
  have hstandard :
      Tendsto S atTop
        (𝓝
          (zetaCompletedExplicitFormulaCorrectionZeroPoleLocalTangentResidueValue f)) :=
    Tendsto.congr' hstandard_event.symm tendsto_const_nhds
  have hdefect : Tendsto D atTop (𝓝 0) :=
    zetaCompletedExplicitFormulaCorrectionZeroPoleTangentOrientationDefect_tendsto_zero
      f F h
  have hsum :
      Tendsto (fun u : ℝ => S u + D u) atTop
        (𝓝
          (zetaCompletedExplicitFormulaCorrectionZeroPoleLocalTangentResidueValue f + 0)) :=
    hstandard.add hdefect
  have hsum_value :
      Tendsto (fun u : ℝ => S u + D u) atTop
        (𝓝
          (zetaCompletedExplicitFormulaCorrectionZeroPoleLocalTangentResidueValue f)) :=
    Eq.subst
      (motive := fun z : ℂ =>
        Tendsto (fun u : ℝ => S u + D u) atTop (𝓝 z))
      (add_zero
        (zetaCompletedExplicitFormulaCorrectionZeroPoleLocalTangentResidueValue f))
      hsum
  have hpoint :
      C = fun u : ℝ => S u + D u := by
    funext u
    exact
      zetaCompletedExplicitFormulaCorrectionZeroPoleScheduledTangentBoundary_eq_standard_add_orientationDefect
        f F h u
  exact Eq.subst
    (motive := fun φ : ℝ → ℂ =>
      Tendsto φ atTop
        (𝓝
          (zetaCompletedExplicitFormulaCorrectionZeroPoleLocalTangentResidueValue f)))
    hpoint.symm
    hsum_value

/-- Source left off-pole decay input for the right zero-pole inversion. -/
theorem zetaCompletedExplicitFormulaCorrectionLeftZeroPoleVerticalIntegral_tendsto_zero_poleKernelSource
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) :
    Tendsto
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaCorrectionLeftZeroPoleVerticalIntegral
          f F (h.height_schedule.height u))
      atTop
      (𝓝 0) := by
  exact
    zetaCompletedExplicitFormulaCorrectionLeftZeroPoleVerticalIntegral_tendsto_zero_ownerLeftOffPoleDecay
      f F h

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
  have hleft :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaCorrectionLeftZeroPoleVerticalIntegral
            f F (h.height_schedule.height u))
        atTop
        (𝓝 0) :=
    zetaCompletedExplicitFormulaCorrectionLeftZeroPoleVerticalIntegral_tendsto_zero_poleKernelSource
      f F h
  have hhorizontal :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaCorrectionZeroPoleScheduledHorizontalDifference
            f F h u)
        atTop
        (𝓝 0) :=
    zetaCompletedExplicitFormulaCorrectionZeroPoleScheduledHorizontalDifference_tendsto_zero_ownerZeroPoleHorizontal
      f F h
  have htangent :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaCorrectionZeroPoleTangentRectangleBoundaryIntegral
            f F (h.height_schedule.height u))
        atTop
        (𝓝
          (zetaCompletedExplicitFormulaCorrectionZeroPoleLocalTangentResidueValue f)) :=
    zetaCompletedExplicitFormulaCorrectionZeroPoleTangentRectangleBoundaryIntegral_tendsto_localTangentResidueValue_poleKernelSource
      f F h
  have hright :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaCorrectionRightZeroPoleVerticalIntegral
            f F (h.height_schedule.height u))
        atTop
        (𝓝
          (zetaCompletedExplicitFormulaCorrectionZeroPoleLocalVerticalResidueValue f)) :=
    zetaCompletedExplicitFormulaCorrectionRightZeroPoleVerticalIntegral_tendsto_localVerticalResidueValue_of_tangentBoundaryResidue_ownerAssembly
      f F h hleft hhorizontal htangent
  have hvalue :
      zetaCompletedExplicitFormulaCorrectionZeroPoleLocalVerticalResidueValue f =
        zetaCompletedExplicitFormulaCorrectionRightZeroPoleVerticalInversionValue f := by
    calc
      zetaCompletedExplicitFormulaCorrectionZeroPoleLocalVerticalResidueValue f =
          -(zetaCompletedExplicitFormulaCorrectionZeroPoleLocalTangentResidueValue f *
            Complex.I) := by
        exact zetaCompletedExplicitFormulaCorrectionZeroPoleLocalVerticalResidueValue_eq f
      _ =
          -(((2 * (Real.pi : ℂ) * Complex.I) *
            (-zetaCompletedExplicitFormulaPhi f (-(1 / 2 : ℂ)))) *
              Complex.I) := by
        exact congrArg
          (fun z : ℂ => -(z * Complex.I))
          (zetaCompletedExplicitFormulaCorrectionZeroPoleLocalTangentResidueValue_eq f)
      _ =
          zetaCompletedExplicitFormulaCorrectionRightZeroPoleVerticalInversionValue f := by
        exact
          (zetaCompletedExplicitFormulaCorrectionRightZeroPoleVerticalInversionValue_eq
            f).symm
  have hright_value :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaCorrectionRightZeroPoleVerticalIntegral
            f F (h.height_schedule.height u))
        atTop
        (𝓝 (zetaCompletedExplicitFormulaCorrectionRightZeroPoleVerticalInversionValue f)) :=
    Eq.subst
      (motive := fun z : ℂ =>
        Tendsto
          (fun u : ℝ =>
            zetaCompletedExplicitFormulaCorrectionRightZeroPoleVerticalIntegral
              f F (h.height_schedule.height u))
          atTop
          (𝓝 z))
      hvalue
      hright
  have hscheduled :
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaCorrectionRightZeroPoleScheduledVerticalInversion
          f F h u) =
      fun u : ℝ =>
        zetaCompletedExplicitFormulaCorrectionRightZeroPoleVerticalIntegral
          f F (h.height_schedule.height u) := by
    funext u
    exact
      zetaCompletedExplicitFormulaCorrectionRightZeroPoleScheduledVerticalInversion_eq_verticalIntegral
        f F h u
  exact Eq.subst
    (motive := fun φ : ℝ → ℂ =>
      Tendsto φ atTop
        (𝓝 (zetaCompletedExplicitFormulaCorrectionRightZeroPoleVerticalInversionValue f)))
    hscheduled.symm
    hright_value

/-- Whole-line Cauchy/Laplace inversion value for the isolated right `s = 0`
pole affine kernel. -/
theorem zetaCompletedExplicitFormulaCorrectionRightZeroPoleAffineKernel_integral_eq_value
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) :
    (∫ t : ℝ,
      zetaCompletedExplicitFormulaCorrectionRightZeroPoleAffineKernel f F t) =
      zetaCompletedExplicitFormulaCorrectionRightZeroPoleVerticalInversionValue f := by
  exact
    zetaCompletedExplicitFormulaCorrectionRightZeroPoleAffineKernel_integral_eq_value_of_scheduledVerticalInversion_tendsto_value
      f F h
      (zetaCompletedExplicitFormulaCorrectionRightZeroPoleScheduledVerticalInversion_tendsto_value_direct
        f F h)

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
    zetaCompletedExplicitFormulaCorrectionRightZeroPoleScheduledVerticalInversion_tendsto_value_direct
      f F h

/-- Right-face zero-pole vertical-inversion limit for the `s = 0`
correction pole, in its contour-side normalization. -/
theorem zetaCompletedExplicitFormulaCorrectionRightZeroPoleVerticalIntegral_tendsto_value_ownerChannelTransportAnalytic
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) :
    Tendsto
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaCorrectionRightZeroPoleVerticalIntegral
          f F (h.height_schedule.height u))
      atTop
      (𝓝 (zetaCompletedExplicitFormulaCorrectionRightZeroPoleVerticalInversionValue f)) := by
  have hinversion :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaCorrectionRightZeroPoleScheduledVerticalInversion
            f F h u)
        atTop
        (𝓝 (zetaCompletedExplicitFormulaCorrectionRightZeroPoleVerticalInversionValue f)) := by
    exact
      zetaCompletedExplicitFormulaCorrectionRightZeroPoleScheduledVerticalInversion_tendsto_value
        f F h
  exact
    zetaCompletedExplicitFormulaCorrectionRightZeroPoleVerticalIntegral_tendsto_of_scheduledVerticalInversion
      f F h hinversion

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
