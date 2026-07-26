import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.ZeroPoleLeftOffPoleAffineTransport

/-!
# Left zero-pole off-pole affine value

This file owns the acyclic affine-window transport for the left face of the
isolated `s = 0` correction pole.  The analytic Cauchy/Laplace leaf lives
downstream; this file only turns that scheduled oscillatory value into the
named affine-window and whole-line formulations.
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

/-- Transport a scheduled off-pole Cauchy/Laplace value for the named left
zero-pole oscillatory integral to the scheduled affine-kernel window. -/
theorem zetaCompletedExplicitFormulaCorrectionLeftZeroPoleAffineKernel_scheduledWindow_tendsto_value_of_scheduledOscillatory_tendsto_value_ownerLeftOffPoleAffineValue
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (value : ℂ)
    (hoscillatory :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaCorrectionLeftZeroPoleScheduledOscillatoryIntegral
            f F h u)
        atTop
        (𝓝 value)) :
    Tendsto
      (fun u : ℝ =>
        ∫ t in Set.Icc
            (-(F.rectangle (h.height_schedule.height u)).T)
            (F.rectangle (h.height_schedule.height u)).T,
          zetaCompletedExplicitFormulaCorrectionLeftZeroPoleAffineKernel f F t)
      atTop
      (𝓝 value) := by
  have hfun :
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaCorrectionLeftZeroPoleScheduledOscillatoryIntegral
          f F h u) =
      (fun u : ℝ =>
        ∫ t in Set.Icc
            (-(F.rectangle (h.height_schedule.height u)).T)
            (F.rectangle (h.height_schedule.height u)).T,
          zetaCompletedExplicitFormulaCorrectionLeftZeroPoleAffineKernel f F t) := by
    funext u
    exact
      zetaCompletedExplicitFormulaCorrectionLeftZeroPoleScheduledOscillatoryIntegral_eq_affineKernelIntegral_ownerLeftOffPoleTransport
        f F h u
  exact
    Eq.subst
      (motive := fun φ : ℝ → ℂ => Tendsto φ atTop (𝓝 value))
      hfun
      hoscillatory

/-- Transport a scheduled off-pole Cauchy/Laplace zero value for the named left
zero-pole oscillatory integral to the scheduled affine-kernel window. -/
theorem zetaCompletedExplicitFormulaCorrectionLeftZeroPoleAffineKernel_scheduledWindow_tendsto_zero_of_scheduledOscillatory_tendsto_zero_ownerLeftOffPoleAffineValue
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (hoscillatory :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaCorrectionLeftZeroPoleScheduledOscillatoryIntegral
            f F h u)
        atTop
        (𝓝 0)) :
    Tendsto
      (fun u : ℝ =>
        ∫ t in Set.Icc
            (-(F.rectangle (h.height_schedule.height u)).T)
            (F.rectangle (h.height_schedule.height u)).T,
          zetaCompletedExplicitFormulaCorrectionLeftZeroPoleAffineKernel f F t)
      atTop
      (𝓝 0) := by
  exact
    zetaCompletedExplicitFormulaCorrectionLeftZeroPoleAffineKernel_scheduledWindow_tendsto_value_of_scheduledOscillatory_tendsto_value_ownerLeftOffPoleAffineValue
      f F h 0
      hoscillatory

/-- Whole-line transport from a separately proved scheduled off-pole
Cauchy/Laplace value. -/
theorem zetaCompletedExplicitFormulaCorrectionLeftZeroPoleAffineKernel_integral_eq_value_of_scheduled_tendsto_value_ownerLeftOffPoleAffineValue
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (value : ℂ)
    (hscheduled :
      Tendsto
        (fun u : ℝ =>
          ∫ t in Set.Icc
              (-(F.rectangle (h.height_schedule.height u)).T)
              (F.rectangle (h.height_schedule.height u)).T,
            zetaCompletedExplicitFormulaCorrectionLeftZeroPoleAffineKernel f F t)
        atTop
        (𝓝 value)) :
    (∫ t : ℝ,
      zetaCompletedExplicitFormulaCorrectionLeftZeroPoleAffineKernel f F t) =
      value := by
  exact
    explicitFormulaScheduledRectangleWindowIntegral_eq_of_tendsto_value
      F
      h.height_schedule.height
      (zetaCompletedExplicitFormulaCorrectionLeftZeroPoleAffineKernel f F)
      value
      h.height_schedule.cofinal
      (zetaCompletedExplicitFormulaCorrectionLeftZeroPoleAffineKernel_integrable_ownerBounds
        f F h)
      hscheduled

/-- Whole-line zero transport from a separately proved scheduled off-pole
Cauchy/Laplace value. -/
theorem zetaCompletedExplicitFormulaCorrectionLeftZeroPoleAffineKernel_integral_eq_zero_of_scheduled_tendsto_zero_ownerLeftOffPoleAffineValue
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (hscheduled :
      Tendsto
        (fun u : ℝ =>
          ∫ t in Set.Icc
              (-(F.rectangle (h.height_schedule.height u)).T)
              (F.rectangle (h.height_schedule.height u)).T,
            zetaCompletedExplicitFormulaCorrectionLeftZeroPoleAffineKernel f F t)
        atTop
        (𝓝 0)) :
    (∫ t : ℝ,
      zetaCompletedExplicitFormulaCorrectionLeftZeroPoleAffineKernel f F t) =
      0 := by
  exact
    zetaCompletedExplicitFormulaCorrectionLeftZeroPoleAffineKernel_integral_eq_value_of_scheduled_tendsto_value_ownerLeftOffPoleAffineValue
      f F h 0
      hscheduled

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
