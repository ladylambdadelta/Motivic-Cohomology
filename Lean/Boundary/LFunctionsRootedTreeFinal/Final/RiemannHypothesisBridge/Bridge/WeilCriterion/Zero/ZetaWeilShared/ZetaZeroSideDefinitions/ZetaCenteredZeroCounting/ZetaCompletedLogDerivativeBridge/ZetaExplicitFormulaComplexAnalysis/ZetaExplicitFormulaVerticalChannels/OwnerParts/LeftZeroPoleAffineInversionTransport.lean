import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.ZeroPoleLeftOffPoleDecay
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.HorizontalEdgeBounds

/-!
# Left zero-pole affine inversion transport

This compatibility file re-exports the left zero-pole affine transport and
whole-line value now owned by `ZeroPoleLeftOffPoleAffineTransport` and
`ZeroPoleLeftOffPoleAffineValue`.
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

/-- Owner-level affine-kernel normal form for the left zero-pole vertical
integrand. -/
theorem zetaCompletedExplicitFormulaCorrectionLeftZeroPoleVerticalIntegrand_eq_affineKernel_ownerTransport
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T t : ℝ) :
    (-1 / zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t) *
        zetaCompletedExplicitFormulaPhi f
          (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t - 1 / 2) =
      zetaCompletedExplicitFormulaCorrectionLeftZeroPoleAffineKernel f F t := by
  exact
    zetaCompletedExplicitFormulaCorrectionLeftZeroPoleVerticalIntegrand_eq_affineKernel_ownerLeftOffPoleTransport
      f F T t

/-- Scheduled left zero-pole vertical cancellation as the named affine kernel
integral. -/
theorem zetaCompletedExplicitFormulaCorrectionLeftZeroPoleScheduledOscillatoryIntegral_eq_affineKernelIntegral_ownerTransport
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    zetaCompletedExplicitFormulaCorrectionLeftZeroPoleScheduledOscillatoryIntegral
        f F h u =
      ∫ t in
          Set.Icc
            (-(F.rectangle (h.height_schedule.height u)).T)
            (F.rectangle (h.height_schedule.height u)).T,
        zetaCompletedExplicitFormulaCorrectionLeftZeroPoleAffineKernel f F t := by
  exact
    zetaCompletedExplicitFormulaCorrectionLeftZeroPoleScheduledOscillatoryIntegral_eq_affineKernelIntegral_ownerLeftOffPoleTransport
      f F h u

/-- Scheduled-window convergence of the left zero-pole affine kernel to its
whole-line integral. -/
theorem zetaCompletedExplicitFormulaCorrectionLeftZeroPoleAffineKernelIntegral_tendsto_integral_ownerTransport
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) :
    Tendsto
      (fun u : ℝ =>
        ∫ t in Set.Icc
            (-(F.rectangle (h.height_schedule.height u)).T)
            (F.rectangle (h.height_schedule.height u)).T,
          zetaCompletedExplicitFormulaCorrectionLeftZeroPoleAffineKernel f F t)
      atTop
      (𝓝 (∫ t : ℝ,
        zetaCompletedExplicitFormulaCorrectionLeftZeroPoleAffineKernel f F t)) := by
  exact
    zetaCompletedExplicitFormulaCorrectionLeftZeroPoleAffineKernelIntegral_tendsto_integral_ownerLeftOffPoleTransport
      f F h

/-- The whole-line left zero-pole affine-kernel integral vanishes. -/
theorem zetaCompletedExplicitFormulaCorrectionLeftZeroPoleAffineKernel_integral_eq_zero_ownerTransport
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) :
    (∫ t : ℝ,
      zetaCompletedExplicitFormulaCorrectionLeftZeroPoleAffineKernel f F t) =
      0 := by
  exact
    zetaCompletedExplicitFormulaCorrectionLeftZeroPoleAffineKernel_integral_eq_zero_ownerLeftOffPoleDecay
      f F h

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
