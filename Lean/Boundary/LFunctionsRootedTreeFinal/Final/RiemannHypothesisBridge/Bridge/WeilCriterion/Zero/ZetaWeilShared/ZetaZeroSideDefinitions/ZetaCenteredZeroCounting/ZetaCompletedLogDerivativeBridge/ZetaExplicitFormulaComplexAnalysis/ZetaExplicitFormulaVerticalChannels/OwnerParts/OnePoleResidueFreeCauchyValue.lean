import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaSinglePoleContour.OwnerParts.CanonicalRawCauchy
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.OnePoleLeftStandardResidueValue
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.RightOnePoleCauchyCancellation

/-!
# Residue-free right one-pole Cauchy value

This file transports the non-circular left standard residue value and finite
raw Cauchy theorem to the scheduled residue-free right `s = 1` correction
value.  Quantitative off-pole and residue-tail estimates live downstream and
must not be used here.
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

/-- The scheduled right `s = 1` affine one-pole kernel has residue-free value
zero, assembled from the direct left standard residue value and the finite
positive-height raw Cauchy theorem.

The remaining analytic leaf in this branch is the left standard residue value
in `OnePoleLeftStandardResidueValue`; this theorem is only the non-circular
right-face transport. -/
theorem zetaCompletedExplicitFormulaCorrectionRightOnePoleAffineKernel_scheduledWindow_tendsto_zero_ownerResidueFreeCauchy
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) :
    Tendsto
      (fun u : ℝ =>
        ∫ t in Set.Icc
            (-(F.rectangle (h.height_schedule.height u)).T)
            (F.rectangle (h.height_schedule.height u)).T,
          zetaCompletedExplicitFormulaCorrectionRightOnePoleAffineKernel f F t)
      atTop
      (𝓝 0) := by
  let B : ℂ :=
    (2 * (Real.pi : ℂ) * Complex.I) *
      (-zetaCompletedExplicitFormulaPhi f (1 / 2))
  have hvertical :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaCorrectionRightOnePoleVerticalIntegral
            f F (h.height_schedule.height u))
        atTop
        (𝓝 0) := by
    have hcancel : B * Complex.I - B * Complex.I = 0 :=
      sub_self (B * Complex.I)
    exact
      zetaCompletedExplicitFormulaCorrectionRightOnePoleVerticalIntegral_tendsto_zero_of_positiveHeight_standardBoundaryResidueValue
        f F h (B * Complex.I) B hcancel
        (zetaCompletedExplicitFormulaCorrectionLeftOnePoleVerticalIntegral_tendsto_standardContourResidue_ownerLeftResidueValue
          f F h)
        (fun T hT =>
          zetaCompletedExplicitFormulaCorrectionOnePoleStandardRectangleBoundaryIntegral_eq_rawCauchy_of_pos_height
            f F h T hT)
  have hfun :
      (fun u : ℝ =>
        ∫ t in Set.Icc
            (-(F.rectangle (h.height_schedule.height u)).T)
            (F.rectangle (h.height_schedule.height u)).T,
          zetaCompletedExplicitFormulaCorrectionRightOnePoleAffineKernel f F t) =
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaCorrectionRightOnePoleVerticalIntegral
          f F (h.height_schedule.height u)) := by
    funext u
    exact
      (zetaCompletedExplicitFormulaCorrectionRightOnePoleVerticalIntegral_eq_affineKernelIntegral_ownerOnePoleVerticalTransport
        f F (h.height_schedule.height u)).symm
  exact
    Eq.subst
      (motive := fun φ : ℝ → ℂ => Tendsto φ atTop (𝓝 0))
      hfun.symm
      hvertical

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
