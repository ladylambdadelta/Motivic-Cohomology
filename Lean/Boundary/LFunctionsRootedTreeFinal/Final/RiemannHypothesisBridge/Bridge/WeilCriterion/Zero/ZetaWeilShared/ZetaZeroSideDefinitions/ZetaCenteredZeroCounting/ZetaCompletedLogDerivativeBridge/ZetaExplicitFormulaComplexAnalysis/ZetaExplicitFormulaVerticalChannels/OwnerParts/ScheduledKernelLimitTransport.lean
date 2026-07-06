import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.AffineVerticalKernels
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.AffineKernelMajorantPackage
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.SymmetricIntegralExhaustion

/-!
# Scheduled kernel limit transport

This file owns small, reusable transport lemmas for moving a scheduled
vertical-channel limit across a pointwise identification with a named kernel
integral.  The analytic estimates remain in the channel-specific files.
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

/-- Transport a scheduled scalar limit across an eventual pointwise equality. -/
theorem explicitFormulaScheduledScalar_tendsto_of_eventually_eq
    (scheduled kernel : ℝ → ℂ) (target : ℂ)
    (hkernel : Tendsto kernel atTop (𝓝 target))
    (hpoint : ∀ᶠ u in atTop, scheduled u = kernel u) :
    Tendsto scheduled atTop (𝓝 target) :=
  hkernel.congr' (hpoint.mono (fun _u hu => hu.symm))

/-- Transport a scheduled scalar limit across a pointwise equality. -/
theorem explicitFormulaScheduledScalar_tendsto_of_forall_eq
    (scheduled kernel : ℝ → ℂ) (target : ℂ)
    (hkernel : Tendsto kernel atTop (𝓝 target))
    (hpoint : ∀ u : ℝ, scheduled u = kernel u) :
    Tendsto scheduled atTop (𝓝 target) :=
  explicitFormulaScheduledScalar_tendsto_of_eventually_eq
    scheduled kernel target hkernel
    (Filter.Eventually.of_forall hpoint)

/-- Compose an unscheduled atTop limit with a cofinal height schedule. -/
theorem explicitFormulaScheduledScalar_tendsto_of_unscheduled
    (kernel : ℝ → ℂ) (height : ℝ → ℝ) (target : ℂ)
    (hkernel : Tendsto kernel atTop (𝓝 target))
    (hheight : Tendsto height atTop atTop) :
    Tendsto (fun u : ℝ => kernel (height u)) atTop (𝓝 target) :=
  hkernel.comp hheight

/-- If the same scheduled scalar converges to its whole-line integral and to a
separately identified value, then the integral is that value.  This is the
generic non-circular assembly step for vertical inversion value theorems: the
exhaustion proof supplies `hintegral`, while the channel-specific Cauchy or
Dirichlet argument supplies `hvalue`. -/
theorem explicitFormulaScheduledScalar_integral_eq_of_tendsto_integral_and_value
    (scheduled : ℝ → ℂ) (integralValue target : ℂ)
    (hintegral : Tendsto scheduled atTop (𝓝 integralValue))
    (hvalue : Tendsto scheduled atTop (𝓝 target)) :
    integralValue = target :=
  tendsto_nhds_unique hintegral hvalue

/-- A contour-family rectangle stores the supplied truncation height, so its
symmetric vertical window is the direct interval `[-T, T]`. -/
theorem explicitFormulaRectangleWindowIntegral_eq_symmetric
    (F : ExplicitFormulaContourFamily) (φ : ℝ → ℂ) (T : ℝ) :
    (∫ t in Set.Icc (-(F.rectangle T).T) (F.rectangle T).T, φ t) =
      ∫ t in Set.Icc (-T) T, φ t :=
  rfl

/-- Transport an unscheduled rectangle-window integral limit from the direct
symmetric-window formulation. -/
theorem explicitFormulaRectangleWindowIntegral_tendsto_of_symmetric
    (F : ExplicitFormulaContourFamily) (φ : ℝ → ℂ) (target : ℂ)
    (hdirect :
      Tendsto
        (fun T : ℝ => ∫ t in Set.Icc (-T) T, φ t)
        atTop
        (𝓝 target)) :
    Tendsto
      (fun T : ℝ =>
        ∫ t in Set.Icc (-(F.rectangle T).T) (F.rectangle T).T, φ t)
      atTop
      (𝓝 target) := by
  have hfun :
      (fun T : ℝ =>
        ∫ t in Set.Icc (-(F.rectangle T).T) (F.rectangle T).T, φ t) =
        (fun T : ℝ => ∫ t in Set.Icc (-T) T, φ t) := by
    funext T
    exact explicitFormulaRectangleWindowIntegral_eq_symmetric F φ T
  exact Eq.subst
    (motive := fun ψ : ℝ → ℂ => Tendsto ψ atTop (𝓝 target))
      hfun.symm
      hdirect

/-- Scheduled rectangle-window integrals of an integrable kernel converge to
the whole-line integral along any cofinal height schedule. -/
theorem explicitFormulaScheduledRectangleWindowIntegral_tendsto_integral
    (F : ExplicitFormulaContourFamily) (height : ℝ → ℝ) (φ : ℝ → ℂ)
    (hheight : Tendsto height atTop atTop)
    (hφ : Integrable φ (volume : Measure ℝ)) :
    Tendsto
      (fun u : ℝ =>
        ∫ t in Set.Icc
            (-(F.rectangle (height u)).T)
            (F.rectangle (height u)).T,
          φ t)
      atTop
      (𝓝 (∫ t : ℝ, φ t)) := by
  let K : ℝ → ℂ := fun T : ℝ =>
    ∫ t in Set.Icc (-(F.rectangle T).T) (F.rectangle T).T, φ t
  have hsymmetric :
      Tendsto
        (fun T : ℝ => ∫ t in Set.Icc (-T) T, φ t)
        atTop
        (𝓝 (∫ t : ℝ, φ t)) :=
    explicitFormulaSymmetricIntervalIntegral_tendsto_integral φ hφ
  have hK :
      Tendsto K atTop (𝓝 (∫ t : ℝ, φ t)) :=
    explicitFormulaRectangleWindowIntegral_tendsto_of_symmetric
      F φ (∫ t : ℝ, φ t) hsymmetric
  exact
    explicitFormulaScheduledScalar_tendsto_of_unscheduled
      K height (∫ t : ℝ, φ t) hK hheight

/-- Scheduled rectangle-window integrals of a kernel with an integrable
majorant package converge to the whole-line integral. -/
theorem explicitFormulaScheduledRectangleWindowIntegral_tendsto_integral_of_majorantPackage
    (F : ExplicitFormulaContourFamily) (height : ℝ → ℝ) (φ : ℝ → ℂ)
    (hheight : Tendsto height atTop atTop)
    (P : ExplicitFormulaAffineKernelMajorantPackage φ) :
    Tendsto
      (fun u : ℝ =>
        ∫ t in Set.Icc
            (-(F.rectangle (height u)).T)
            (F.rectangle (height u)).T,
          φ t)
      atTop
      (𝓝 (∫ t : ℝ, φ t)) :=
  explicitFormulaScheduledRectangleWindowIntegral_tendsto_integral
    F height φ hheight P.integrable

/-- A scheduled rectangle-window limit identifies the whole-line integral of an
integrable kernel, once the height schedule is cofinal.

This is the neutral exhaustion/uniqueness step used by value theorems whose
analytic content is a scheduled contour limit.  The channel-specific file owns
the scheduled limit; this lemma owns only the measure-theoretic passage from
scheduled windows to the whole-line integral. -/
theorem explicitFormulaScheduledRectangleWindowIntegral_eq_of_tendsto_value
    (F : ExplicitFormulaContourFamily) (height : ℝ → ℝ)
    (φ : ℝ → ℂ) (target : ℂ)
    (hheight : Tendsto height atTop atTop)
    (hφ : Integrable φ (volume : Measure ℝ))
    (hvalue :
      Tendsto
        (fun u : ℝ =>
          ∫ t in Set.Icc
              (-(F.rectangle (height u)).T)
              (F.rectangle (height u)).T,
            φ t)
        atTop
        (𝓝 target)) :
    (∫ t : ℝ, φ t) = target := by
  let S : ℝ → ℂ := fun u : ℝ =>
    ∫ t in Set.Icc
        (-(F.rectangle (height u)).T)
        (F.rectangle (height u)).T,
      φ t
  have hS_integral :
      Tendsto S atTop (𝓝 (∫ t : ℝ, φ t)) :=
    explicitFormulaScheduledRectangleWindowIntegral_tendsto_integral
      F height φ hheight hφ
  exact
    explicitFormulaScheduledScalar_integral_eq_of_tendsto_integral_and_value
      S (∫ t : ℝ, φ t) target hS_integral hvalue

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
