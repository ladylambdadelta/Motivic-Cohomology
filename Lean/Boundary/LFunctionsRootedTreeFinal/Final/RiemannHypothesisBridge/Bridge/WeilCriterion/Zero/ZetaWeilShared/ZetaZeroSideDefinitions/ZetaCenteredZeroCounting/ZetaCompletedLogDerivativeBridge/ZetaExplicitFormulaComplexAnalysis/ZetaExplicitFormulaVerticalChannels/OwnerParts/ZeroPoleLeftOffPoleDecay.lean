import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.ZeroPoleLeftOffPoleAffineValue
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.ZeroPoleLeftOffPoleCauchyValue

/-!
# Left zero-pole projection-residue value

This file owns compatibility wrappers for the corrected left face of the
isolated `s = 0` correction pole.  The left face carries the right Cauchy
projection plus the tangent residue term; downstream pole-face subtraction
cancels the shared projection.
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

/-- Compatibility wrapper: scheduled Cauchy/Laplace value of the left `s = 0`
correction affine kernel in the corrected projection-residue normalization. -/
theorem zetaCompletedExplicitFormulaCorrectionLeftZeroPoleAffineKernel_scheduledWindow_tendsto_projectionResidue_ownerLeftOffPoleDecay
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
    zetaCompletedExplicitFormulaCorrectionLeftZeroPoleAffineKernel_scheduledWindow_tendsto_value_of_scheduledOscillatory_tendsto_value_ownerLeftOffPoleAffineValue
      f F h
      (Boundary.zetaLaplaceTransform_rightZeroPoleCauchyProjectionValue
          f.toZetaTestFunction' F.c +
        zetaCompletedExplicitFormulaCorrectionZeroPoleLocalTangentResidueValue
          f * Complex.I)
      (zetaCompletedExplicitFormulaCorrectionLeftZeroPoleScheduledOscillatoryIntegral_tendsto_projectionResidue_ownerLeftOffPoleCauchy
        f F h)

/-- Transport form of the left `s = 0` value theorem. -/
theorem zetaCompletedExplicitFormulaCorrectionLeftZeroPoleAffineKernel_integral_eq_projectionResidue_of_scheduled_tendsto_projectionResidue_ownerLeftOffPoleDecay
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
        (𝓝
          (Boundary.zetaLaplaceTransform_rightZeroPoleCauchyProjectionValue
              f.toZetaTestFunction' F.c +
            zetaCompletedExplicitFormulaCorrectionZeroPoleLocalTangentResidueValue
              f * Complex.I))) :
    (∫ t : ℝ,
      zetaCompletedExplicitFormulaCorrectionLeftZeroPoleAffineKernel f F t) =
      Boundary.zetaLaplaceTransform_rightZeroPoleCauchyProjectionValue
          f.toZetaTestFunction' F.c +
        zetaCompletedExplicitFormulaCorrectionZeroPoleLocalTangentResidueValue
          f * Complex.I := by
  exact
    zetaCompletedExplicitFormulaCorrectionLeftZeroPoleAffineKernel_integral_eq_value_of_scheduled_tendsto_value_ownerLeftOffPoleAffineValue
      f F h
      (Boundary.zetaLaplaceTransform_rightZeroPoleCauchyProjectionValue
          f.toZetaTestFunction' F.c +
        zetaCompletedExplicitFormulaCorrectionZeroPoleLocalTangentResidueValue
          f * Complex.I)
      hscheduled

/-- Compatibility wrapper for the whole-line left `s = 0` correction affine
kernel value. -/
theorem zetaCompletedExplicitFormulaCorrectionLeftZeroPoleAffineKernel_integral_eq_projectionResidue_ownerLeftOffPoleDecay
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) :
    (∫ t : ℝ,
      zetaCompletedExplicitFormulaCorrectionLeftZeroPoleAffineKernel f F t) =
      Boundary.zetaLaplaceTransform_rightZeroPoleCauchyProjectionValue
          f.toZetaTestFunction' F.c +
        zetaCompletedExplicitFormulaCorrectionZeroPoleLocalTangentResidueValue
          f * Complex.I := by
  exact
    zetaCompletedExplicitFormulaCorrectionLeftZeroPoleAffineKernel_integral_eq_projectionResidue_of_scheduled_tendsto_projectionResidue_ownerLeftOffPoleDecay
      f F h
      (zetaCompletedExplicitFormulaCorrectionLeftZeroPoleAffineKernel_scheduledWindow_tendsto_projectionResidue_ownerLeftOffPoleDecay
        f F h)

/-- Owner scheduled theorem: the left `s = 0` correction face has the corrected
projection-residue scheduled limit. -/
theorem zetaCompletedExplicitFormulaCorrectionLeftZeroPoleVerticalIntegral_tendsto_projectionResidue_ownerLeftOffPoleDecay
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) :
    Tendsto
      (fun u : ℝ =>
          zetaCompletedExplicitFormulaCorrectionLeftZeroPoleVerticalIntegral
            f F (h.height_schedule.height u))
      atTop
      (𝓝
        (Boundary.zetaLaplaceTransform_rightZeroPoleCauchyProjectionValue
            f.toZetaTestFunction' F.c +
          zetaCompletedExplicitFormulaCorrectionZeroPoleLocalTangentResidueValue
            f * Complex.I)) := by
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
        Boundary.zetaLaplaceTransform_rightZeroPoleCauchyProjectionValue
            f.toZetaTestFunction' F.c +
          zetaCompletedExplicitFormulaCorrectionZeroPoleLocalTangentResidueValue
            f * Complex.I :=
    zetaCompletedExplicitFormulaCorrectionLeftZeroPoleAffineKernel_integral_eq_projectionResidue_ownerLeftOffPoleDecay
      f F h
  have hK_value :
      Tendsto K atTop
        (𝓝
          (Boundary.zetaLaplaceTransform_rightZeroPoleCauchyProjectionValue
              f.toZetaTestFunction' F.c +
            zetaCompletedExplicitFormulaCorrectionZeroPoleLocalTangentResidueValue
              f * Complex.I)) := by
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
    (motive := fun φ : ℝ → ℂ =>
      Tendsto φ atTop
        (𝓝
          (Boundary.zetaLaplaceTransform_rightZeroPoleCauchyProjectionValue
              f.toZetaTestFunction' F.c +
            zetaCompletedExplicitFormulaCorrectionZeroPoleLocalTangentResidueValue
              f * Complex.I)))
    hpoint.symm
    hK_value

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
