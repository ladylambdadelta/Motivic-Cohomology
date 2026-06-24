import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.CorrectionPoleSides
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.PrimeScheduledChannels
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.ScheduledBoundaryIdentities
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.ScheduledKernelLimitTransport
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.SymmetricIntegralExhaustion
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.ZeroPoleAffineKernelIntegrability

/-!
# Left zero-pole off-pole affine transport

This file owns only the acyclic transport from the scheduled left `s = 0`
vertical face to the named left zero-pole affine kernel.  It deliberately does
not import the cancellation or Cauchy-assembly files that consume the left
off-pole decay theorem.
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

/-- The left zero-pole vertical integrand is the named left affine kernel. -/
theorem zetaCompletedExplicitFormulaCorrectionLeftZeroPoleVerticalIntegrand_eq_affineKernel_ownerLeftOffPoleTransport
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T t : ℝ) :
    (-1 / zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t) *
        zetaCompletedExplicitFormulaPhi f
          (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t - 1 / 2) =
      zetaCompletedExplicitFormulaCorrectionLeftZeroPoleAffineKernel f F t := by
  have hpath :
      zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t =
        zetaCompletedExplicitFormulaLeftAffineLine F t := by
    exact zetaCompletedExplicitFormulaPrime_leftPath_eq_affineLine F T t
  have hshift :
      zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t - (1 / 2 : ℂ) =
        zetaCompletedExplicitFormulaLeftCenteredAffineLine F t := by
    exact zetaCompletedExplicitFormulaPrime_shiftedLeftPath_eq_affineLine F T t
  calc
    (-1 / zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t) *
        zetaCompletedExplicitFormulaPhi f
          (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t - 1 / 2) =
      (-1 / zetaCompletedExplicitFormulaLeftAffineLine F t) *
        zetaCompletedExplicitFormulaPhi f
          (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t - 1 / 2) := by
        exact congrArg
          (fun z : ℂ =>
            (-1 / z) *
              zetaCompletedExplicitFormulaPhi f
                (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t - 1 / 2))
          hpath
    _ =
      (-1 / zetaCompletedExplicitFormulaLeftAffineLine F t) *
        zetaCompletedExplicitFormulaPhi f
          (zetaCompletedExplicitFormulaLeftCenteredAffineLine F t) := by
        exact congrArg
          (fun z : ℂ =>
            (-1 / zetaCompletedExplicitFormulaLeftAffineLine F t) *
              zetaCompletedExplicitFormulaPhi f z)
          hshift
    _ = zetaCompletedExplicitFormulaCorrectionLeftZeroPoleAffineKernel f F t := by
        rfl

/-- The scheduled left zero-pole vertical integral is the scheduled window of
the named left affine kernel. -/
theorem zetaCompletedExplicitFormulaCorrectionLeftZeroPoleVerticalIntegral_eq_affineKernelIntegral_ownerLeftOffPoleTransport
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    zetaCompletedExplicitFormulaCorrectionLeftZeroPoleVerticalIntegral
        f F (h.height_schedule.height u) =
      ∫ t in
          Set.Icc
            (-(F.rectangle (h.height_schedule.height u)).T)
            (F.rectangle (h.height_schedule.height u)).T,
        zetaCompletedExplicitFormulaCorrectionLeftZeroPoleAffineKernel f F t := by
  have hfun :
      (fun t : ℝ =>
        (-1 /
            zetaCompletedExplicitFormulaLeftPath
              (F.rectangle (h.height_schedule.height u)) t) *
          zetaCompletedExplicitFormulaPhi f
            (zetaCompletedExplicitFormulaLeftPath
                (F.rectangle (h.height_schedule.height u)) t - 1 / 2)) =
      (fun t : ℝ =>
        zetaCompletedExplicitFormulaCorrectionLeftZeroPoleAffineKernel f F t) := by
    funext t
    exact
      zetaCompletedExplicitFormulaCorrectionLeftZeroPoleVerticalIntegrand_eq_affineKernel_ownerLeftOffPoleTransport
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

/-- Scheduled left zero-pole vertical cancellation as the named affine kernel
integral. -/
theorem zetaCompletedExplicitFormulaCorrectionLeftZeroPoleScheduledOscillatoryIntegral_eq_affineKernelIntegral_ownerLeftOffPoleTransport
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
    Eq.trans
      (zetaCompletedExplicitFormulaCorrectionLeftZeroPoleVerticalIntegral_eq_scheduledOscillatoryIntegral
        f F h u).symm
      (zetaCompletedExplicitFormulaCorrectionLeftZeroPoleVerticalIntegral_eq_affineKernelIntegral_ownerLeftOffPoleTransport
        f F h u)

/-- Scheduled-window convergence of the left zero-pole affine kernel to its
whole-line integral. -/
theorem zetaCompletedExplicitFormulaCorrectionLeftZeroPoleAffineKernelIntegral_tendsto_integral_ownerLeftOffPoleTransport
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
  let K : ℝ → ℂ := fun T : ℝ =>
    ∫ t in Set.Icc
        (-(F.rectangle T).T)
        (F.rectangle T).T,
      zetaCompletedExplicitFormulaCorrectionLeftZeroPoleAffineKernel f F t
  have hsymmetric :
      Tendsto
        (fun T : ℝ =>
          ∫ t in Set.Icc (-T) T,
            zetaCompletedExplicitFormulaCorrectionLeftZeroPoleAffineKernel f F t)
        atTop
        (𝓝 (∫ t : ℝ,
          zetaCompletedExplicitFormulaCorrectionLeftZeroPoleAffineKernel f F t)) :=
    explicitFormulaSymmetricIntervalIntegral_tendsto_integral
      (zetaCompletedExplicitFormulaCorrectionLeftZeroPoleAffineKernel f F)
      (zetaCompletedExplicitFormulaCorrectionLeftZeroPoleAffineKernel_integrable_ownerBounds
        f F h)
  have hkernel :
      Tendsto K atTop
        (𝓝 (∫ t : ℝ,
          zetaCompletedExplicitFormulaCorrectionLeftZeroPoleAffineKernel f F t)) :=
    explicitFormulaRectangleWindowIntegral_tendsto_of_symmetric
      F
      (zetaCompletedExplicitFormulaCorrectionLeftZeroPoleAffineKernel f F)
      (∫ t : ℝ,
        zetaCompletedExplicitFormulaCorrectionLeftZeroPoleAffineKernel f F t)
      hsymmetric
  exact
    explicitFormulaScheduledScalar_tendsto_of_unscheduled
      K
      h.height_schedule.height
      (∫ t : ℝ,
        zetaCompletedExplicitFormulaCorrectionLeftZeroPoleAffineKernel f F t)
      hkernel
      h.height_schedule.cofinal

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
