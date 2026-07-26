import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.LeftZeroPoleAffineInversionTransport
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.OnePoleAffineInversionTransport
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.RightZeroPoleLocalCauchyValue

/-!
# Whole-line values of the elementary correction affine kernels

This file owns the recombination from isolated zero-pole and one-pole affine
values to the total elementary correction affine values on the right and left
vertical faces.
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

/-- Whole-line value of the total right elementary correction affine kernel in
the one-sided projection normalization for the right `s = 0` pole. -/
theorem zetaCompletedExplicitFormulaCorrectionRightAffineKernel_integral_eq_projection_ownerCorrectionAffineValues
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) :
    (∫ t : ℝ,
      zetaCompletedExplicitFormulaCorrectionRightAffineKernel f F t) =
      Boundary.zetaLaplaceTransform_rightZeroPoleCauchyProjectionValue
          f.toZetaTestFunction' F.c +
        zetaCompletedExplicitFormulaRightOnePoleCauchyProjectionValue f F.c := by
  have hzero_int :
      Integrable
        (zetaCompletedExplicitFormulaCorrectionRightZeroPoleAffineKernel f F)
        (volume : Measure ℝ) :=
    zetaCompletedExplicitFormulaCorrectionRightZeroPoleAffineKernel_integrable_ownerBounds
      f F h
  have hone_int :
      Integrable
        (zetaCompletedExplicitFormulaCorrectionRightOnePoleAffineKernel f F)
        (volume : Measure ℝ) :=
    zetaCompletedExplicitFormulaCorrectionRightOnePoleAffineKernel_integrable_ownerBounds
      f F h
  have hsum :
      (∫ t : ℝ,
        zetaCompletedExplicitFormulaCorrectionRightZeroPoleAffineKernel f F t +
          zetaCompletedExplicitFormulaCorrectionRightOnePoleAffineKernel f F t) =
        (∫ t : ℝ,
          zetaCompletedExplicitFormulaCorrectionRightZeroPoleAffineKernel f F t) +
          ∫ t : ℝ,
            zetaCompletedExplicitFormulaCorrectionRightOnePoleAffineKernel f F t :=
    integral_add hzero_int hone_int
  have hpoint :
      (zetaCompletedExplicitFormulaCorrectionRightAffineKernel f F) =ᵐ[volume]
        fun t : ℝ =>
          zetaCompletedExplicitFormulaCorrectionRightZeroPoleAffineKernel f F t +
            zetaCompletedExplicitFormulaCorrectionRightOnePoleAffineKernel f F t :=
    Filter.Eventually.of_forall
      (fun t =>
        zetaCompletedExplicitFormulaCorrectionRightAffineKernel_eq_zeroPole_add_onePole
          f F t)
  have hzero_value :
      (∫ t : ℝ,
        zetaCompletedExplicitFormulaCorrectionRightZeroPoleAffineKernel f F t) =
        Boundary.zetaLaplaceTransform_rightZeroPoleCauchyProjectionValue
          f.toZetaTestFunction' F.c :=
    zetaCompletedExplicitFormulaCorrectionRightZeroPoleAffineKernel_integral_eq_projection_directOffPoleCauchy
      f F
  have hone_value :
      (∫ t : ℝ,
        zetaCompletedExplicitFormulaCorrectionRightOnePoleAffineKernel f F t) =
        zetaCompletedExplicitFormulaRightOnePoleCauchyProjectionValue f F.c :=
    zetaCompletedExplicitFormulaCorrectionRightOnePoleAffineKernel_integral_eq_projection_ownerTransport
      f F h
  calc
    (∫ t : ℝ,
      zetaCompletedExplicitFormulaCorrectionRightAffineKernel f F t) =
        ∫ t : ℝ,
          zetaCompletedExplicitFormulaCorrectionRightZeroPoleAffineKernel f F t +
            zetaCompletedExplicitFormulaCorrectionRightOnePoleAffineKernel f F t := by
      exact integral_congr_ae hpoint
    _ =
        (∫ t : ℝ,
          zetaCompletedExplicitFormulaCorrectionRightZeroPoleAffineKernel f F t) +
          ∫ t : ℝ,
            zetaCompletedExplicitFormulaCorrectionRightOnePoleAffineKernel f F t := by
      exact hsum
    _ =
        Boundary.zetaLaplaceTransform_rightZeroPoleCauchyProjectionValue
            f.toZetaTestFunction' F.c +
          ∫ t : ℝ,
            zetaCompletedExplicitFormulaCorrectionRightOnePoleAffineKernel f F t := by
      exact congrArg
        (fun z : ℂ =>
          z +
            ∫ t : ℝ,
              zetaCompletedExplicitFormulaCorrectionRightOnePoleAffineKernel f F t)
        hzero_value
    _ =
        Boundary.zetaLaplaceTransform_rightZeroPoleCauchyProjectionValue
            f.toZetaTestFunction' F.c +
          zetaCompletedExplicitFormulaRightOnePoleCauchyProjectionValue f F.c := by
      exact congrArg
        (fun z : ℂ =>
          Boundary.zetaLaplaceTransform_rightZeroPoleCauchyProjectionValue
              f.toZetaTestFunction' F.c + z)
        hone_value

/-- Whole-line value of the total left elementary correction affine kernel in
the corrected projection-residue normalization. -/
theorem zetaCompletedExplicitFormulaCorrectionLeftAffineKernel_integral_eq_projectionResidue_ownerCorrectionAffineValues
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) :
    (∫ t : ℝ,
      zetaCompletedExplicitFormulaCorrectionLeftAffineKernel f F t) =
      (Boundary.zetaLaplaceTransform_rightZeroPoleCauchyProjectionValue
          f.toZetaTestFunction' F.c +
        zetaCompletedExplicitFormulaCorrectionZeroPoleLocalTangentResidueValue
          f * Complex.I) +
        (((2 * (Real.pi : ℂ) * Complex.I) *
          (-zetaCompletedExplicitFormulaPhi f (1 / 2))) * Complex.I +
            zetaCompletedExplicitFormulaRightOnePoleCauchyProjectionValue f F.c) := by
  let A : ℂ :=
    Boundary.zetaLaplaceTransform_rightZeroPoleCauchyProjectionValue
      f.toZetaTestFunction' F.c +
      zetaCompletedExplicitFormulaCorrectionZeroPoleLocalTangentResidueValue
        f * Complex.I
  let B : ℂ :=
    ((2 * (Real.pi : ℂ) * Complex.I) *
      (-zetaCompletedExplicitFormulaPhi f (1 / 2))) * Complex.I
  let P : ℂ :=
    zetaCompletedExplicitFormulaRightOnePoleCauchyProjectionValue f F.c
  have hzero_int :
      Integrable
        (zetaCompletedExplicitFormulaCorrectionLeftZeroPoleAffineKernel f F)
        (volume : Measure ℝ) :=
    zetaCompletedExplicitFormulaCorrectionLeftZeroPoleAffineKernel_integrable_ownerBounds
      f F h
  have hone_int :
      Integrable
        (zetaCompletedExplicitFormulaCorrectionLeftOnePoleAffineKernel f F)
        (volume : Measure ℝ) :=
    zetaCompletedExplicitFormulaCorrectionLeftOnePoleAffineKernel_integrable_ownerBounds
      f F h
  have hsum :
      (∫ t : ℝ,
        zetaCompletedExplicitFormulaCorrectionLeftZeroPoleAffineKernel f F t +
          zetaCompletedExplicitFormulaCorrectionLeftOnePoleAffineKernel f F t) =
        (∫ t : ℝ,
          zetaCompletedExplicitFormulaCorrectionLeftZeroPoleAffineKernel f F t) +
          ∫ t : ℝ,
            zetaCompletedExplicitFormulaCorrectionLeftOnePoleAffineKernel f F t :=
    integral_add hzero_int hone_int
  have hpoint :
      (zetaCompletedExplicitFormulaCorrectionLeftAffineKernel f F) =ᵐ[volume]
        fun t : ℝ =>
          zetaCompletedExplicitFormulaCorrectionLeftZeroPoleAffineKernel f F t +
            zetaCompletedExplicitFormulaCorrectionLeftOnePoleAffineKernel f F t :=
    Filter.Eventually.of_forall
      (fun t =>
        zetaCompletedExplicitFormulaCorrectionLeftAffineKernel_eq_zeroPole_add_onePole
          f F t)
  have hzero_value :
      (∫ t : ℝ,
        zetaCompletedExplicitFormulaCorrectionLeftZeroPoleAffineKernel f F t) =
        A := by
    unfold A
    exact
      zetaCompletedExplicitFormulaCorrectionLeftZeroPoleAffineKernel_integral_eq_projectionResidue_ownerTransport
      f F h
  have hone_value :
      (∫ t : ℝ,
        zetaCompletedExplicitFormulaCorrectionLeftOnePoleAffineKernel f F t) =
        B + P :=
    zetaCompletedExplicitFormulaCorrectionLeftOnePoleAffineKernel_integral_eq_projectionResidue_ownerTransport
      f F h
  calc
    (∫ t : ℝ,
      zetaCompletedExplicitFormulaCorrectionLeftAffineKernel f F t) =
        ∫ t : ℝ,
          zetaCompletedExplicitFormulaCorrectionLeftZeroPoleAffineKernel f F t +
            zetaCompletedExplicitFormulaCorrectionLeftOnePoleAffineKernel f F t := by
      exact integral_congr_ae hpoint
    _ =
        (∫ t : ℝ,
          zetaCompletedExplicitFormulaCorrectionLeftZeroPoleAffineKernel f F t) +
          ∫ t : ℝ,
            zetaCompletedExplicitFormulaCorrectionLeftOnePoleAffineKernel f F t := by
      exact hsum
    _ =
        A +
          ∫ t : ℝ,
            zetaCompletedExplicitFormulaCorrectionLeftOnePoleAffineKernel f F t := by
      exact congrArg
        (fun z : ℂ =>
          z +
            ∫ t : ℝ,
              zetaCompletedExplicitFormulaCorrectionLeftOnePoleAffineKernel f F t)
        hzero_value
    _ = A + (B + P) := by
      exact congrArg (fun z : ℂ => A + z) hone_value
    _ =
        (Boundary.zetaLaplaceTransform_rightZeroPoleCauchyProjectionValue
            f.toZetaTestFunction' F.c +
          zetaCompletedExplicitFormulaCorrectionZeroPoleLocalTangentResidueValue
            f * Complex.I) +
          (((2 * (Real.pi : ℂ) * Complex.I) *
            (-zetaCompletedExplicitFormulaPhi f (1 / 2))) * Complex.I +
              zetaCompletedExplicitFormulaRightOnePoleCauchyProjectionValue f F.c) := by
      rfl

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
