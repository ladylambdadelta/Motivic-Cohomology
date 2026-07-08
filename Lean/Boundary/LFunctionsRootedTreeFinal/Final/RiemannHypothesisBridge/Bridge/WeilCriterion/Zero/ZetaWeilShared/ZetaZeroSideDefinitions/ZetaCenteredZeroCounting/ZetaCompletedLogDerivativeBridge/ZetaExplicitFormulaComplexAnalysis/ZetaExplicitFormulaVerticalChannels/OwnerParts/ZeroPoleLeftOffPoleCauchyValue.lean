import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.PoleKernelVerticalInversion
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.PoleKernelVerticalInversionEstimate
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.ZeroPoleLeftOffPoleAffineTransport
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.ZeroPoleHorizontalEdgeBounds
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.ZeroPoleSquarePuncturedProjectBridge
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.ZeroPoleTangentBoundaryAlgebra

/-!
# Left zero-pole off-pole Cauchy value

This file owns the Cauchy/Laplace decay theorem for the scheduled left `s = 0`
off-pole face.  This is an analytic leaf: it must not be proved from the right
zero-pole value theorem, because that theorem consumes this left off-pole decay.
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

/-- Direct right-face local residue value for the isolated `s = 0` correction
pole, stated before the left off-pole Cauchy value consumes it. -/
theorem zetaCompletedExplicitFormulaCorrectionRightZeroPoleVerticalIntegral_tendsto_localRawResidue_ownerLeftOffPoleCauchy
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) :
    Tendsto
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaCorrectionRightZeroPoleVerticalIntegral
          f F (h.height_schedule.height u))
      atTop
      (𝓝 (-(((2 * (Real.pi : ℂ) * Complex.I) *
        (-zetaCompletedExplicitFormulaPhi f (-(1 / 2 : ℂ)))) * Complex.I))) := by
  have hvalue :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaCorrectionRightZeroPoleVerticalIntegral
            f F (h.height_schedule.height u))
        atTop
        (𝓝 (zetaCompletedExplicitFormulaCorrectionRightZeroPoleVerticalInversionValue f)) :=
    zetaCompletedExplicitFormulaCorrectionRightZeroPoleVerticalIntegral_tendsto_value_ownerChannelTransportAnalytic
      f F h
  have hvalue_eq :
      zetaCompletedExplicitFormulaCorrectionRightZeroPoleVerticalInversionValue f =
        -(((2 * (Real.pi : ℂ) * Complex.I) *
          (-zetaCompletedExplicitFormulaPhi f (-(1 / 2 : ℂ)))) * Complex.I) := by
    exact
      zetaCompletedExplicitFormulaCorrectionRightZeroPoleVerticalInversionValue_eq
        f
  exact
    Eq.subst
      (motive := fun z : ℂ =>
        Tendsto
          (fun u : ℝ =>
            zetaCompletedExplicitFormulaCorrectionRightZeroPoleVerticalIntegral
              f F (h.height_schedule.height u))
          atTop
          (𝓝 z))
      hvalue_eq
      hvalue

/-- Scheduled raw standard Cauchy residue in the local tangent-residue
normalization. -/
theorem zetaCompletedExplicitFormulaCorrectionZeroPole_eventually_standardBoundaryLocalTangentResidueValue_ownerLeftOffPoleCauchy
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) :
    ∀ᶠ u in atTop,
      zetaCompletedExplicitFormulaCorrectionZeroPoleStandardRectangleBoundaryIntegral
        f F (h.height_schedule.height u) =
        zetaCompletedExplicitFormulaCorrectionZeroPoleLocalTangentResidueValue f := by
  exact h.height_schedule.eventually_height_pos.mono
    (fun u hu =>
      zetaCompletedExplicitFormulaCorrectionZeroPoleStandardRectangleBoundaryIntegral_eq_localTangentResidueValue_of_pos_height
        f F h hu)

/-- The scheduled orientation defect for the isolated `s = 0` tangent boundary
tends to zero, using the owner horizontal-edge estimate. -/
theorem zetaCompletedExplicitFormulaCorrectionZeroPoleTangentOrientationDefect_tendsto_zero_ownerLeftOffPoleCauchy
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) :
    Tendsto
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaCorrectionZeroPoleTangentOrientationDefect
          f F (h.height_schedule.height u))
      atTop
      (𝓝 0) := by
  have hhorizontal :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaCorrectionZeroPoleScheduledHorizontalDifference
            f F h u)
        atTop
        (𝓝 0) :=
    zetaCompletedExplicitFormulaCorrectionZeroPoleScheduledHorizontalDifference_tendsto_zero_ownerZeroPoleHorizontal
      f F h
  have hsum :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaCorrectionZeroPoleScheduledHorizontalDifference
              f F h u +
            zetaCompletedExplicitFormulaCorrectionZeroPoleScheduledHorizontalDifference
              f F h u)
        atTop
        (𝓝 (0 + 0)) :=
    hhorizontal.add hhorizontal
  have hsum_zero :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaCorrectionZeroPoleScheduledHorizontalDifference
              f F h u +
            zetaCompletedExplicitFormulaCorrectionZeroPoleScheduledHorizontalDifference
              f F h u)
        atTop
        (𝓝 0) :=
    Eq.subst
      (motive := fun z : ℂ =>
        Tendsto
          (fun u : ℝ =>
            zetaCompletedExplicitFormulaCorrectionZeroPoleScheduledHorizontalDifference
                f F h u +
              zetaCompletedExplicitFormulaCorrectionZeroPoleScheduledHorizontalDifference
                f F h u)
          atTop
          (𝓝 z))
      (add_zero (0 : ℂ))
      hsum
  have hpoint :
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaCorrectionZeroPoleTangentOrientationDefect
          f F (h.height_schedule.height u)) =
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaCorrectionZeroPoleScheduledHorizontalDifference
            f F h u +
          zetaCompletedExplicitFormulaCorrectionZeroPoleScheduledHorizontalDifference
            f F h u) := by
    funext u
    exact
      zetaCompletedExplicitFormulaCorrectionZeroPoleScheduledOrientationDefect_eq_horizontal_add_horizontal
        f F h u
  exact
    Eq.subst
      (motive := fun φ : ℝ → ℂ => Tendsto φ atTop (𝓝 0))
      hpoint.symm
      hsum_zero

/-- Scheduled Cauchy/Laplace value for the left `s = 0` off-pole affine kernel.

The pole lies off this left vertical line, so the scheduled affine windows
vanish by the off-pole Cauchy/Laplace estimate. -/
theorem zetaCompletedExplicitFormulaCorrectionLeftZeroPoleAffineKernel_scheduledWindow_tendsto_zero_ownerLeftOffPoleCauchy
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
  let B : ℂ :=
    (2 * (Real.pi : ℂ) * Complex.I) *
      (-zetaCompletedExplicitFormulaPhi f (-(1 / 2 : ℂ)))
  have hosc :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaCorrectionLeftZeroPoleScheduledOscillatoryIntegral
            f F h u)
        atTop
        (𝓝 0) := by
    have hcancel : -(B * Complex.I) + B * Complex.I = 0 :=
      neg_add_cancel (B * Complex.I)
    exact
      zetaCompletedExplicitFormulaCorrectionLeftZeroPoleScheduledOscillatoryIntegral_tendsto_zero_of_standardBoundaryResidue_and_orientationDefect_ownerZeroPoleAlgebra
        f F h (-(B * Complex.I)) B
        (zetaCompletedExplicitFormulaCorrectionRightZeroPoleVerticalIntegral_tendsto_localRawResidue_ownerLeftOffPoleCauchy
          f F h)
        hcancel
        (h.height_schedule.eventually_height_pos.mono
          (fun u hu =>
            zetaCompletedExplicitFormulaCorrectionZeroPoleStandardRectangleBoundaryIntegral_eq_rawCauchy_of_pos_height
              f F h (T := h.height_schedule.height u) hu))
        (zetaCompletedExplicitFormulaCorrectionZeroPoleTangentOrientationDefect_tendsto_zero_ownerLeftOffPoleCauchy
          f F h)
        (zetaCompletedExplicitFormulaCorrectionZeroPoleScheduledHorizontalDifference_tendsto_zero_ownerZeroPoleHorizontal
          f F h)
  have hfun :
      (fun u : ℝ =>
        ∫ t in Set.Icc
            (-(F.rectangle (h.height_schedule.height u)).T)
            (F.rectangle (h.height_schedule.height u)).T,
          zetaCompletedExplicitFormulaCorrectionLeftZeroPoleAffineKernel f F t) =
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaCorrectionLeftZeroPoleScheduledOscillatoryIntegral
          f F h u) := by
    funext u
    exact
      (zetaCompletedExplicitFormulaCorrectionLeftZeroPoleScheduledOscillatoryIntegral_eq_affineKernelIntegral_ownerLeftOffPoleTransport
        f F h u).symm
  exact
    Eq.subst
      (motive := fun φ : ℝ → ℂ => Tendsto φ atTop (𝓝 0))
      hfun.symm
      hosc

/-- Whole-line Cauchy/Laplace value for the left `s = 0` off-pole affine kernel,
transported from scheduled-window off-pole Cauchy decay. -/
theorem zetaCompletedExplicitFormulaCorrectionLeftZeroPoleAffineKernel_integral_eq_zero_ownerLeftOffPoleCauchy
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) :
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
      (zetaCompletedExplicitFormulaCorrectionLeftZeroPoleAffineKernel_scheduledWindow_tendsto_zero_ownerLeftOffPoleCauchy
        f F h)

/-- Owner Cauchy/Laplace value: the scheduled left zero-pole off-pole oscillatory
integral tends to zero.

This is the independent off-pole analytic leaf.  Its proof should use the
left affine kernel normal form, off-pole Cauchy/Laplace decay, and horizontal
normalization, not the right zero-pole inversion value. -/
theorem zetaCompletedExplicitFormulaCorrectionLeftZeroPoleScheduledOscillatoryIntegral_tendsto_zero_ownerLeftOffPoleCauchy
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) :
    Tendsto
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaCorrectionLeftZeroPoleScheduledOscillatoryIntegral
          f F h u)
      atTop
      (𝓝 0) := by
  let K : ℝ → ℂ := fun u : ℝ =>
    ∫ t in Set.Icc
        (-(F.rectangle (h.height_schedule.height u)).T)
        (F.rectangle (h.height_schedule.height u)).T,
      zetaCompletedExplicitFormulaCorrectionLeftZeroPoleAffineKernel f F t
  have hK_zero :
      Tendsto K atTop (𝓝 0) := by
    unfold K
    exact
      zetaCompletedExplicitFormulaCorrectionLeftZeroPoleAffineKernel_scheduledWindow_tendsto_zero_ownerLeftOffPoleCauchy
        f F h
  have hpoint :
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaCorrectionLeftZeroPoleScheduledOscillatoryIntegral
          f F h u) =
      K := by
    funext u
    exact
      zetaCompletedExplicitFormulaCorrectionLeftZeroPoleScheduledOscillatoryIntegral_eq_affineKernelIntegral_ownerLeftOffPoleTransport
        f F h u
  exact
    Eq.subst
      (motive := fun φ : ℝ → ℂ => Tendsto φ atTop (𝓝 0))
      hpoint.symm
      hK_zero

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
