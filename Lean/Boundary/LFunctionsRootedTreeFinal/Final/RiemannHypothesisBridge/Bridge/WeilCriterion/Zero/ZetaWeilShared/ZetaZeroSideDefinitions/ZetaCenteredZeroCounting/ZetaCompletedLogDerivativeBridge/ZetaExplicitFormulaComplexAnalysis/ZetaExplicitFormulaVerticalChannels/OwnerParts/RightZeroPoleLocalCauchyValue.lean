import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.RightZeroPoleAffineInversionTransport
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaTransformCalculus.ZetaTransformCauchyProjection.ZeroPoleProjection.Owner

/-!
# Right zero-pole local Cauchy value

This file owns the independent right-face Cauchy/Laplace value for the isolated
`s = 0` correction pole.  It is upstream of the left off-pole decay theorem.
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

/-- Pointwise transport from the explicit-formula right zero-pole affine kernel
to the transform-calculus Cauchy kernel. -/
theorem zetaCompletedExplicitFormulaCorrectionRightZeroPoleAffineKernel_eq_transformCauchyKernel_directOffPoleCauchy
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (t : ℝ) :
    zetaCompletedExplicitFormulaCorrectionRightZeroPoleAffineKernel f F t =
      (-1 / ((F.c : ℂ) + (t : ℂ) * Complex.I)) *
        Boundary.zetaLaplaceTransform f.toZetaTestFunction'
          (((F.c : ℂ) - (1 / 2 : ℂ)) + (t : ℂ) * Complex.I) := by
  have hkernel :
      zetaCompletedExplicitFormulaCorrectionRightZeroPoleAffineKernel f F t =
        (-1 / ((F.c : ℂ) + t * Complex.I)) *
          zetaCompletedExplicitFormulaPhi f
            (((F.c : ℂ) - (1 / 2 : ℂ)) + t * Complex.I) := by
    exact
      (zetaCompletedExplicitFormulaCorrectionRightZeroPoleVerticalInversionIntegrand_eq_affineKernel_ownerTransport
        f F 0 t).symm.trans
        (zetaCompletedExplicitFormulaCorrectionRightZeroPoleVerticalInversionIntegrand_eq_affineLine
          f F 0 t)
  have hphi :
      zetaCompletedExplicitFormulaPhi f
          (((F.c : ℂ) - (1 / 2 : ℂ)) + t * Complex.I) =
        Boundary.zetaLaplaceTransform f.toZetaTestFunction'
          (((F.c : ℂ) - (1 / 2 : ℂ)) + t * Complex.I) := by
    exact
      congrFun
        (zetaCompletedExplicitFormulaPhi_eq_laplace f)
        (((F.c : ℂ) - (1 / 2 : ℂ)) + t * Complex.I)
  exact
    Eq.trans
      hkernel
      (congrArg
        (fun z : ℂ =>
          (-1 / ((F.c : ℂ) + t * Complex.I)) * z)
        hphi)

/-- Direct whole-line Cauchy/Laplace value for the isolated right `s = 0`
affine pole kernel in its one-sided transform-calculus normalization.

This is the value actually supplied by the fixed right-line Cauchy projection:
it is a half-line projection of the time-side kernel, not the closed-contour
local residue by itself. -/
theorem zetaCompletedExplicitFormulaCorrectionRightZeroPoleAffineKernel_integral_eq_projection_directOffPoleCauchy
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) :
    (∫ t : ℝ,
      zetaCompletedExplicitFormulaCorrectionRightZeroPoleAffineKernel f F t) =
      Boundary.zetaLaplaceTransform_rightZeroPoleCauchyProjectionValue
        f.toZetaTestFunction' F.c := by
  have hkernel :
      (∫ t : ℝ,
        zetaCompletedExplicitFormulaCorrectionRightZeroPoleAffineKernel f F t) =
        ∫ t : ℝ,
          (-1 / ((F.c : ℂ) + (t : ℂ) * Complex.I)) *
            Boundary.zetaLaplaceTransform f.toZetaTestFunction'
              (((F.c : ℂ) - (1 / 2 : ℂ)) + (t : ℂ) * Complex.I) := by
    exact
      integral_congr_ae
        (Filter.Eventually.of_forall
          (fun t : ℝ =>
            zetaCompletedExplicitFormulaCorrectionRightZeroPoleAffineKernel_eq_transformCauchyKernel_directOffPoleCauchy
              f F t))
  have hprojection :
      (∫ t : ℝ,
          (-1 / ((F.c : ℂ) + (t : ℂ) * Complex.I)) *
            Boundary.zetaLaplaceTransform f.toZetaTestFunction'
              (((F.c : ℂ) - (1 / 2 : ℂ)) + (t : ℂ) * Complex.I)) =
        Boundary.zetaLaplaceTransform_rightZeroPoleCauchyProjectionValue
          f.toZetaTestFunction' F.c :=
    Boundary.zetaLaplaceTransform_rightZeroPoleProjectionKernel_fullLineCauchyValue
      f F.c F.c_pos
  exact hkernel.trans hprojection

/-- Projection-valued right-face convergence for the isolated `s = 0` pole.

This is the non-residue form directly obtained from the fixed-line Cauchy
projection theorem and scheduled affine-kernel exhaustion. -/
theorem zetaCompletedExplicitFormulaCorrectionRightZeroPoleScheduledVerticalInversion_tendsto_projection_directOffPoleCauchy
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) :
    Tendsto
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaCorrectionRightZeroPoleScheduledVerticalInversion
          f F h u)
      atTop
      (𝓝
        (Boundary.zetaLaplaceTransform_rightZeroPoleCauchyProjectionValue
          f.toZetaTestFunction' F.c)) := by
  exact
    zetaCompletedExplicitFormulaCorrectionRightZeroPoleScheduledVerticalInversion_tendsto_of_affineKernel_integral_eq_ownerTransport
      f F h
      (Boundary.zetaLaplaceTransform_rightZeroPoleCauchyProjectionValue
        f.toZetaTestFunction' F.c)
      (zetaCompletedExplicitFormulaCorrectionRightZeroPoleAffineKernel_integral_eq_projection_directOffPoleCauchy
        f F)

/-- Projection-valued convergence for the named right zero-pole vertical
integral. -/
theorem zetaCompletedExplicitFormulaCorrectionRightZeroPoleVerticalIntegral_tendsto_projection_directOffPoleCauchy
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) :
    Tendsto
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaCorrectionRightZeroPoleVerticalIntegral
          f F (h.height_schedule.height u))
      atTop
      (𝓝
        (Boundary.zetaLaplaceTransform_rightZeroPoleCauchyProjectionValue
          f.toZetaTestFunction' F.c)) := by
  exact
    zetaCompletedExplicitFormulaCorrectionRightZeroPoleVerticalIntegral_tendsto_of_scheduledVerticalInversion_value
      f F h
      (Boundary.zetaLaplaceTransform_rightZeroPoleCauchyProjectionValue
        f.toZetaTestFunction' F.c)
      (zetaCompletedExplicitFormulaCorrectionRightZeroPoleScheduledVerticalInversion_tendsto_projection_directOffPoleCauchy
        f F h)

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
