import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.ZeroPoleLeftOffPoleAffineTransport
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.ZeroPoleLeftOffPoleCauchyValue

/-!
# Left zero-pole off-pole affine value

This file owns the off-pole affine value theorem for the left face of the
isolated `s = 0` correction pole.  The analytic leaf is the scheduled
Cauchy/Laplace value; the whole-line value is the corresponding exhaustion
transport.
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
      (motive := fun φ : ℝ → ℂ => Tendsto φ atTop (𝓝 0))
      hfun
      hoscillatory

/-- Owner analytic leaf: scheduled off-pole Cauchy/Laplace value of the left
`s = 0` correction affine kernel.

Proof target:
off-pole Cauchy/Laplace estimate on the left affine line, plus the rapid decay
of `Phi_f`.  This theorem is upstream of scheduled rectangle exhaustion and
must not be proved from `ZeroPoleLeftOffPoleDecay` or left-zero cancellation
consumers. -/
theorem zetaCompletedExplicitFormulaCorrectionLeftZeroPoleAffineKernel_scheduledWindow_tendsto_zero_ownerLeftOffPoleAffineValue
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) :
    Tendsto
      (fun u : ℝ =>
        ∫ t in Set.Icc
            (-(F.rectangle (h.height_schedule.height u)).T)
            (F.rectangle (h.height_schedule.height u)).T,
          zetaCompletedExplicitFormulaCorrectionLeftZeroPoleAffineKernel f F t)
      atTop
      (𝓝 0) := by
  have hoscillatory :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaCorrectionLeftZeroPoleScheduledOscillatoryIntegral
            f F h u)
        atTop
        (𝓝 0) := by
    exact
      zetaCompletedExplicitFormulaCorrectionLeftZeroPoleScheduledOscillatoryIntegral_tendsto_zero_ownerLeftOffPoleCauchy
        f F h
  exact
    zetaCompletedExplicitFormulaCorrectionLeftZeroPoleAffineKernel_scheduledWindow_tendsto_zero_of_scheduledOscillatory_tendsto_zero_ownerLeftOffPoleAffineValue
      f F h hoscillatory

/-- Whole-line transport from a separately proved scheduled off-pole
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
    explicitFormulaScheduledRectangleWindowIntegral_eq_of_tendsto_value
      F
      h.height_schedule.height
      (zetaCompletedExplicitFormulaCorrectionLeftZeroPoleAffineKernel f F)
      0
      h.height_schedule.cofinal
      (zetaCompletedExplicitFormulaCorrectionLeftZeroPoleAffineKernel_integrable_ownerBounds
        f F h)
      hscheduled

/-- Owner whole-line value: the left `s = 0` correction affine kernel has zero
integral, transported from the scheduled off-pole Cauchy/Laplace value. -/
theorem zetaCompletedExplicitFormulaCorrectionLeftZeroPoleAffineKernel_integral_eq_zero_ownerLeftOffPoleAffineValue
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) :
    (∫ t : ℝ,
      zetaCompletedExplicitFormulaCorrectionLeftZeroPoleAffineKernel f F t) =
      0 := by
  exact
    zetaCompletedExplicitFormulaCorrectionLeftZeroPoleAffineKernel_integral_eq_zero_of_scheduled_tendsto_zero_ownerLeftOffPoleAffineValue
      f F h
      (zetaCompletedExplicitFormulaCorrectionLeftZeroPoleAffineKernel_scheduledWindow_tendsto_zero_ownerLeftOffPoleAffineValue
        f F h)

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
