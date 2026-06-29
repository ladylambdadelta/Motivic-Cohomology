import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.ZeroPoleLeftOffPoleAffineValue

/-!
# Left zero-pole off-pole decay

This file owns the analytic decay theorem for the left face of the isolated
`s = 0` correction pole.  The left face is off the pole, so this theorem must
come from off-pole Cauchy/Laplace estimates and Paley-Wiener decay, not from a
centered right zero-pole residue normalization.
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

/-- Compatibility wrapper: scheduled off-pole Cauchy/Laplace value of the left
`s = 0` correction affine kernel.

The finite/scheduled contour estimate is owned upstream in
`ZeroPoleLeftOffPoleAffineValue`, which in turn consumes the named Cauchy
value leaf.  This file retains the historical decay-layer name for downstream
left-face consumers. -/
theorem zetaCompletedExplicitFormulaCorrectionLeftZeroPoleAffineKernel_scheduledWindow_tendsto_zero_ownerLeftOffPoleDecay
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
  exact
    zetaCompletedExplicitFormulaCorrectionLeftZeroPoleAffineKernel_scheduledWindow_tendsto_zero_ownerLeftOffPoleAffineValue
      f F h

/-- Transport form of the left `s = 0` off-pole value theorem.

Once the finite/scheduled Cauchy argument proves that the scheduled windows of
the left affine zero-pole kernel tend to `0`, integrability and rectangle
exhaustion identify the whole-line affine integral with the same value.  This
is the same non-circular assembly step used for the right `s = 1` off-pole
kernel; it does not use downstream left-zero cancellation. -/
theorem zetaCompletedExplicitFormulaCorrectionLeftZeroPoleAffineKernel_integral_eq_zero_of_scheduled_tendsto_zero_ownerLeftOffPoleDecay
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
    zetaCompletedExplicitFormulaCorrectionLeftZeroPoleAffineKernel_integral_eq_zero_of_scheduled_tendsto_zero_ownerLeftOffPoleAffineValue
      f F h
      hscheduled

/-- Compatibility wrapper for the whole-line left `s = 0` correction affine
kernel value.

The analytic owner theorem is
`zetaCompletedExplicitFormulaCorrectionLeftZeroPoleAffineKernel_integral_eq_zero_ownerLeftOffPoleAffineValue`
in `ZeroPoleLeftOffPoleAffineValue.lean`.  This local name is kept for
downstream consumers of the decay owner. -/
theorem zetaCompletedExplicitFormulaCorrectionLeftZeroPoleAffineKernel_integral_eq_zero_ownerLeftOffPoleDecay
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) :
    (∫ t : ℝ,
      zetaCompletedExplicitFormulaCorrectionLeftZeroPoleAffineKernel f F t) =
      0 := by
  exact
    zetaCompletedExplicitFormulaCorrectionLeftZeroPoleAffineKernel_integral_eq_zero_of_scheduled_tendsto_zero_ownerLeftOffPoleDecay
      f F h
      (zetaCompletedExplicitFormulaCorrectionLeftZeroPoleAffineKernel_scheduledWindow_tendsto_zero_ownerLeftOffPoleDecay
        f F h)

/-- Owner scheduled theorem: the left `s = 0` correction face has zero scheduled
limit because the left face is off the isolated pole.

This theorem is now only transport from the whole-line left affine-kernel value
through the scheduled rectangle exhaustion. -/
theorem zetaCompletedExplicitFormulaCorrectionLeftZeroPoleVerticalIntegral_tendsto_zero_ownerLeftOffPoleDecay
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) :
    Tendsto
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaCorrectionLeftZeroPoleVerticalIntegral
          f F (h.height_schedule.height u))
      atTop
      (𝓝 0) := by
  let K : ℝ → ℂ := fun u : ℝ =>
    ∫ t in Set.Icc
        (-(F.rectangle (h.height_schedule.height u)).T)
        (F.rectangle (h.height_schedule.height u)).T,
      zetaCompletedExplicitFormulaCorrectionLeftZeroPoleAffineKernel f F t
  have hK_integral :
      Tendsto K atTop
        (𝓝 (∫ t : ℝ,
          zetaCompletedExplicitFormulaCorrectionLeftZeroPoleAffineKernel f F t)) :=
    zetaCompletedExplicitFormulaCorrectionLeftZeroPoleAffineKernelIntegral_tendsto_integral_ownerLeftOffPoleTransport
      f F h
  have hvalue :
      (∫ t : ℝ,
        zetaCompletedExplicitFormulaCorrectionLeftZeroPoleAffineKernel f F t) =
        0 :=
    zetaCompletedExplicitFormulaCorrectionLeftZeroPoleAffineKernel_integral_eq_zero_ownerLeftOffPoleDecay
      f F h
  have hK_zero : Tendsto K atTop (𝓝 0) := by
    exact Eq.subst
      (motive := fun z : ℂ => Tendsto K atTop (𝓝 z))
      hvalue
      hK_integral
  have hpoint :
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaCorrectionLeftZeroPoleVerticalIntegral
          f F (h.height_schedule.height u)) =
        K := by
    funext u
    exact
      zetaCompletedExplicitFormulaCorrectionLeftZeroPoleVerticalIntegral_eq_affineKernelIntegral_ownerLeftOffPoleTransport
        f F h u
  exact Eq.subst
    (motive := fun φ : ℝ → ℂ => Tendsto φ atTop (𝓝 0))
    hpoint.symm
    hK_zero

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
