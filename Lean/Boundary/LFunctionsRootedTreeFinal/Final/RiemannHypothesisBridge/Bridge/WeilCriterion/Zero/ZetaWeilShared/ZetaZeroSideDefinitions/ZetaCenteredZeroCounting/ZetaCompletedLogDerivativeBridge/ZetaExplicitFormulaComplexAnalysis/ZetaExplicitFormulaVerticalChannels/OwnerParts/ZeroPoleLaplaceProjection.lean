import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.RightZeroPoleAffineInversionTransport
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.ZeroPoleCenteredCauchyValue
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.RightZeroPoleCauchyAssembly
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.ZeroPoleHorizontalEdgeBounds
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.ZeroPoleSquarePuncturedProjectBridge
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.CorrectionPoleResidues
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.ZeroPoleLeftOffPoleDecay

/-!
# Zero-pole right vertical value

This file owns the genuine analytic value theorem for the isolated right
`s = 0` correction pole after centering `z = s - 1 / 2`.

In centered coordinates the right affine kernel is

```text
  (-1 / (z + 1/2)) * Phi_f z
```

on a vertical line.  The pole of this kernel is at `z = -1/2`, so the
contour-side value samples `Phi_f (-1/2)`.  It is deliberately not identified
with the centered completed correction contribution at `Phi_f 0` in this file.
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

/-- The scheduled zero-pole tangent boundary has the shifted local tangent
residue value.

This is the honest finite-contour input for the right zero-pole vertical value:
the standard rectangle residue samples `Phi_f (-1/2)`, and the project tangent
orientation defect tends to zero through the isolated horizontal estimate. -/
theorem zetaCompletedExplicitFormulaCorrectionZeroPoleTangentRectangleBoundaryIntegral_tendsto_localTangentResidueValue_ownerLaplaceProjection
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
          f F h.phi_control hu)
  have hstandard :
      Tendsto S atTop
        (𝓝
          (zetaCompletedExplicitFormulaCorrectionZeroPoleLocalTangentResidueValue f)) :=
    hstandard_event.tendsto_iff.2 tendsto_const_nhds
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

/-- Owner obligation for the left zero-pole off-pole face.

The left face does not contain the `s = 0` pole.  Its decay should be proved
from the off-pole Cauchy/Laplace estimate for the left affine kernel, not from
the downstream right zero-pole value theorem. -/
theorem zetaCompletedExplicitFormulaCorrectionLeftZeroPoleVerticalIntegral_tendsto_zero_ownerLaplaceProjection
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

/-- Scheduled right zero-pole vertical inversion at the shifted local
contour-side value.

This combines the shifted tangent residue value, left zero-pole decay, and
isolated horizontal decay. -/
theorem zetaCompletedExplicitFormulaCorrectionRightZeroPoleScheduledVerticalInversion_tendsto_value_of_tangentResidue_ownerLaplaceProjection
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
    zetaCompletedExplicitFormulaCorrectionLeftZeroPoleVerticalIntegral_tendsto_zero_ownerLaplaceProjection
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
    zetaCompletedExplicitFormulaCorrectionZeroPoleTangentRectangleBoundaryIntegral_tendsto_localTangentResidueValue_ownerLaplaceProjection
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

/-- Owner analytic leaf: whole-line right vertical value for the isolated
right zero-pole affine kernel.

This is the true missing theorem behind the scheduled right zero-pole
inversion.  It should be proved by the contour argument for the displayed
kernel, including the tangent-to-real-vertical orientation factor. -/
theorem zetaCompletedExplicitFormulaCorrectionRightZeroPoleAffineKernel_integral_eq_value_ownerLaplaceProjection
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) :
    (∫ t : ℝ,
      zetaCompletedExplicitFormulaCorrectionRightZeroPoleAffineKernel f F t) =
      zetaCompletedExplicitFormulaCorrectionRightZeroPoleVerticalInversionValue f := by
  exact
    zetaCompletedExplicitFormulaCorrectionRightZeroPoleAffineKernel_integral_eq_value_of_scheduledVerticalInversion_tendsto_value_ownerTransport
      f F h
      (zetaCompletedExplicitFormulaCorrectionRightZeroPoleScheduledVerticalInversion_tendsto_value_of_tangentResidue_ownerLaplaceProjection
        f F h)

/-- Scheduled right zero-pole vertical inversion as a pure transport
consequence of the whole-line right vertical value. -/
theorem zetaCompletedExplicitFormulaCorrectionRightZeroPoleScheduledVerticalInversion_tendsto_value_ownerLaplaceProjection
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) :
    Tendsto
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaCorrectionRightZeroPoleScheduledVerticalInversion
          f F h u)
      atTop
      (𝓝 (zetaCompletedExplicitFormulaCorrectionRightZeroPoleVerticalInversionValue f)) := by
  exact
    zetaCompletedExplicitFormulaCorrectionRightZeroPoleScheduledVerticalInversion_tendsto_value_of_tangentResidue_ownerLaplaceProjection
      f F h

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
