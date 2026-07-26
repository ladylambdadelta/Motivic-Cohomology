import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.PoleKernelVerticalInversion
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.RightZeroPoleLocalCauchyValue
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.ZeroPoleLeftOffPoleAffineTransport
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.ZeroPoleHorizontalEdgeBounds
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.ZeroPoleSquarePuncturedProjectBridge
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.ZeroPoleTangentBoundaryAlgebra

/-!
# Left zero-pole off-pole Cauchy value

This file owns the Cauchy/Laplace decay theorem for the scheduled left `s = 0`
off-pole face.  The independent right-face local residue is imported from the
right zero-pole Cauchy owner and used only as a non-circular input to the
tangent-boundary cancellation.
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

/-- Scheduled tangent rectangle boundary convergence to the local raw tangent
residue. -/
theorem zetaCompletedExplicitFormulaCorrectionZeroPoleTangentRectangleBoundaryIntegral_tendsto_localTangentResidue_directOffPoleCauchy
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) :
    Tendsto
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaCorrectionZeroPoleTangentRectangleBoundaryIntegral
          f F (h.height_schedule.height u))
      atTop
      (𝓝
        (zetaCompletedExplicitFormulaCorrectionZeroPoleLocalTangentResidueValue
          f)) := by
  let standard : ℝ → ℂ := fun u : ℝ =>
    zetaCompletedExplicitFormulaCorrectionZeroPoleStandardRectangleBoundaryIntegral
      f F (h.height_schedule.height u)
  let orientationDefect : ℝ → ℂ := fun u : ℝ =>
    zetaCompletedExplicitFormulaCorrectionZeroPoleTangentOrientationDefect
      f F (h.height_schedule.height u)
  let tangent : ℝ → ℂ := fun u : ℝ =>
    zetaCompletedExplicitFormulaCorrectionZeroPoleTangentRectangleBoundaryIntegral
      f F (h.height_schedule.height u)
  let B : ℂ :=
    zetaCompletedExplicitFormulaCorrectionZeroPoleLocalTangentResidueValue f
  have hstandard_event :
      Filter.EventuallyEq atTop standard (fun u : ℝ => B) := by
    unfold standard
    unfold B
    exact
      zetaCompletedExplicitFormulaCorrectionZeroPole_eventually_standardBoundaryLocalTangentResidueValue_ownerLeftOffPoleCauchy
        f F h
  have hstandard : Tendsto standard atTop (𝓝 B) :=
    Tendsto.congr' hstandard_event.symm tendsto_const_nhds
  have horientation : Tendsto orientationDefect atTop (𝓝 0) := by
    unfold orientationDefect
    exact
      zetaCompletedExplicitFormulaCorrectionZeroPoleTangentOrientationDefect_tendsto_zero_ownerLeftOffPoleCauchy
        f F h
  have hsum :
      Tendsto
        (fun u : ℝ => standard u + orientationDefect u)
        atTop
        (𝓝 (B + 0)) :=
    hstandard.add horientation
  have hsum_value :
      Tendsto
        (fun u : ℝ => standard u + orientationDefect u)
        atTop
        (𝓝 B) :=
    Eq.subst
      (motive := fun value : ℂ =>
        Tendsto
          (fun u : ℝ => standard u + orientationDefect u)
          atTop
          (𝓝 value))
      (add_zero B)
      hsum
  have htangent :
      tangent =
        (fun u : ℝ => standard u + orientationDefect u) := by
    funext u
    unfold tangent
    unfold standard
    unfold orientationDefect
    exact
      zetaCompletedExplicitFormulaCorrectionZeroPoleScheduledTangentBoundary_eq_standard_add_orientationDefect
        f F h u
  have htangent_tendsto : Tendsto tangent atTop (𝓝 B) :=
    Eq.subst
      (motive := fun φ : ℝ → ℂ => Tendsto φ atTop (𝓝 B))
      htangent.symm
      hsum_value
  exact htangent_tendsto

/-- Corrected scheduled Cauchy/Laplace value for the left `s = 0` face.

The fixed right-line Cauchy theorem gives the right zero-pole projection.  The
orientation identity then forces the scheduled left face to carry that same
projection plus the tangent residue term; this is the non-circular replacement
for the former zero-valued off-pole assertion. -/
theorem zetaCompletedExplicitFormulaCorrectionLeftZeroPoleScheduledOscillatoryIntegral_tendsto_projectionResidue_directOffPoleCauchy
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) :
    Tendsto
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaCorrectionLeftZeroPoleScheduledOscillatoryIntegral
          f F h u)
      atTop
      (𝓝
        (Boundary.zetaLaplaceTransform_rightZeroPoleCauchyProjectionValue
            f.toZetaTestFunction' F.c +
          zetaCompletedExplicitFormulaCorrectionZeroPoleLocalTangentResidueValue
            f * Complex.I)) := by
  let A : ℂ :=
    Boundary.zetaLaplaceTransform_rightZeroPoleCauchyProjectionValue
      f.toZetaTestFunction' F.c
  let B : ℂ :=
    zetaCompletedExplicitFormulaCorrectionZeroPoleLocalTangentResidueValue f
  have hright :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaCorrectionRightZeroPoleVerticalIntegral
            f F (h.height_schedule.height u))
        atTop
        (𝓝 A) := by
    unfold A
    exact
      zetaCompletedExplicitFormulaCorrectionRightZeroPoleVerticalIntegral_tendsto_projection_directOffPoleCauchy
        f F h
  have htangent :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaCorrectionZeroPoleTangentRectangleBoundaryIntegral
            f F (h.height_schedule.height u))
        atTop
        (𝓝 B) := by
    unfold B
    exact
      zetaCompletedExplicitFormulaCorrectionZeroPoleTangentRectangleBoundaryIntegral_tendsto_localTangentResidue_directOffPoleCauchy
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
  have hleft :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaCorrectionLeftZeroPoleScheduledOscillatoryIntegral
            f F h u)
        atTop
        (𝓝 (A + B * Complex.I)) :=
    zetaCompletedExplicitFormulaCorrectionLeftZeroPoleScheduledOscillatoryIntegral_tendsto_right_add_tangent_mul_I_of_right_tangent_horizontal_ownerZeroPoleAlgebra
      f F h A B hright htangent hhorizontal
  exact hleft

/-- Corrected scheduled value for the left `s = 0` affine kernel. -/
theorem zetaCompletedExplicitFormulaCorrectionLeftZeroPoleAffineKernel_scheduledWindow_tendsto_projectionResidue_directOffPoleCauchy
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) :
    Tendsto
      (fun u : ℝ =>
        ∫ t in Set.Icc
            (-(F.rectangle (h.height_schedule.height u)).T)
            (F.rectangle (h.height_schedule.height u)).T,
          zetaCompletedExplicitFormulaCorrectionLeftZeroPoleAffineKernel f F t)
      atTop
      (𝓝
        (Boundary.zetaLaplaceTransform_rightZeroPoleCauchyProjectionValue
            f.toZetaTestFunction' F.c +
          zetaCompletedExplicitFormulaCorrectionZeroPoleLocalTangentResidueValue
            f * Complex.I)) := by
  have hwindow :
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
  exact Eq.subst
    (motive := fun φ : ℝ → ℂ =>
      Tendsto φ atTop
        (𝓝
          (Boundary.zetaLaplaceTransform_rightZeroPoleCauchyProjectionValue
              f.toZetaTestFunction' F.c +
            zetaCompletedExplicitFormulaCorrectionZeroPoleLocalTangentResidueValue
              f * Complex.I)))
    hwindow.symm
    (zetaCompletedExplicitFormulaCorrectionLeftZeroPoleScheduledOscillatoryIntegral_tendsto_projectionResidue_directOffPoleCauchy
      f F h)

/-- Owner scheduled Cauchy/Laplace value for the left `s = 0` affine kernel. -/
theorem zetaCompletedExplicitFormulaCorrectionLeftZeroPoleAffineKernel_scheduledWindow_tendsto_projectionResidue_ownerLeftOffPoleCauchy
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) :
    Tendsto
      (fun u : ℝ =>
        ∫ t in Set.Icc
            (-(F.rectangle (h.height_schedule.height u)).T)
            (F.rectangle (h.height_schedule.height u)).T,
          zetaCompletedExplicitFormulaCorrectionLeftZeroPoleAffineKernel f F t)
      atTop
      (𝓝
        (Boundary.zetaLaplaceTransform_rightZeroPoleCauchyProjectionValue
            f.toZetaTestFunction' F.c +
          zetaCompletedExplicitFormulaCorrectionZeroPoleLocalTangentResidueValue
            f * Complex.I)) := by
  exact
    zetaCompletedExplicitFormulaCorrectionLeftZeroPoleAffineKernel_scheduledWindow_tendsto_projectionResidue_directOffPoleCauchy
      f F h

/-- Whole-line Cauchy/Laplace value for the left `s = 0` affine kernel,
transported from the corrected scheduled value. -/
theorem zetaCompletedExplicitFormulaCorrectionLeftZeroPoleAffineKernel_integral_eq_projectionResidue_ownerLeftOffPoleCauchy
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) :
    (∫ t : ℝ,
      zetaCompletedExplicitFormulaCorrectionLeftZeroPoleAffineKernel f F t) =
      Boundary.zetaLaplaceTransform_rightZeroPoleCauchyProjectionValue
          f.toZetaTestFunction' F.c +
        zetaCompletedExplicitFormulaCorrectionZeroPoleLocalTangentResidueValue
          f * Complex.I := by
  exact
    explicitFormulaScheduledRectangleWindowIntegral_eq_of_tendsto_value
      F
      h.height_schedule.height
      (zetaCompletedExplicitFormulaCorrectionLeftZeroPoleAffineKernel f F)
      (Boundary.zetaLaplaceTransform_rightZeroPoleCauchyProjectionValue
          f.toZetaTestFunction' F.c +
        zetaCompletedExplicitFormulaCorrectionZeroPoleLocalTangentResidueValue
          f * Complex.I)
      h.height_schedule.cofinal
      (zetaCompletedExplicitFormulaCorrectionLeftZeroPoleAffineKernel_integrable_ownerBounds
        f F h)
      (zetaCompletedExplicitFormulaCorrectionLeftZeroPoleAffineKernel_scheduledWindow_tendsto_projectionResidue_ownerLeftOffPoleCauchy
        f F h)

/-- Owner Cauchy/Laplace value for the scheduled left zero-pole oscillatory
integral. -/
theorem zetaCompletedExplicitFormulaCorrectionLeftZeroPoleScheduledOscillatoryIntegral_tendsto_projectionResidue_ownerLeftOffPoleCauchy
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) :
    Tendsto
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaCorrectionLeftZeroPoleScheduledOscillatoryIntegral
          f F h u)
      atTop
      (𝓝
        (Boundary.zetaLaplaceTransform_rightZeroPoleCauchyProjectionValue
            f.toZetaTestFunction' F.c +
          zetaCompletedExplicitFormulaCorrectionZeroPoleLocalTangentResidueValue
            f * Complex.I)) := by
  exact
    zetaCompletedExplicitFormulaCorrectionLeftZeroPoleScheduledOscillatoryIntegral_tendsto_projectionResidue_directOffPoleCauchy
      f F h

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
