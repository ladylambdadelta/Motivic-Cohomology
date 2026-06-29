import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.OnePoleResidueTailEstimate

/-!
# Left one-pole projection-corrected residue value

This file owns the scheduled left-face value for the isolated `s = 1`
correction pole after accounting for the right Cauchy/Laplace projection.
Its proof is a limit wrapper over the quantitative inverse-quadratic
residue-tail owner theorem, not over any downstream right off-pole decay
consumer.
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

/-- Owner analytic leaf: direct left-face projection-corrected residue value
for the `s = 1` correction pole.

The intended proof is the left one-pole contour shift with the right off-pole
face kept out of the argument: apply the local Cauchy residue theorem at
`s = 1`, use horizontal decay for the standard boundary, and pass to the
scheduled left vertical face. -/
theorem zetaCompletedExplicitFormulaCorrectionLeftOnePoleVerticalIntegral_tendsto_projectionResidue_ownerLeftResidueValue
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) :
    Tendsto
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaCorrectionLeftOnePoleVerticalIntegral
          f F (h.height_schedule.height u))
      atTop
      (𝓝 (((2 * (Real.pi : ℂ) * Complex.I) *
        (-zetaCompletedExplicitFormulaPhi f (1 / 2))) * Complex.I +
        zetaCompletedExplicitFormulaRightOnePoleCauchyProjectionValue f F.c)) := by
  let A : ℂ :=
    ((2 * (Real.pi : ℂ) * Complex.I) *
      (-zetaCompletedExplicitFormulaPhi f (1 / 2))) * Complex.I +
      zetaCompletedExplicitFormulaRightOnePoleCauchyProjectionValue f F.c
  match
    zetaCompletedExplicitFormulaCorrectionLeftOnePoleVerticalIntegral_eventual_inverseQuadratic_to_projectionResidue_ownerResidueTail
      f F h with
  | ⟨ML, _hMLpos, hbound⟩ =>
      have hmajorant :
          Tendsto
            (fun u : ℝ =>
              ML *
                (1 + ‖(F.rectangle (h.height_schedule.height u)).T‖) ^
                  (-(2 : ℤ)))
            atTop
            (𝓝 0) :=
        zetaCompletedExplicitFormulaCorrection_scheduledInverseQuadraticTailMajorant_tendsto_zero
          F h.height_schedule ML
      exact
        tendsto_iff_norm_sub_tendsto_zero.2
          (squeeze_zero'
            (Eventually.of_forall
              (fun u : ℝ =>
                norm_nonneg
                  (zetaCompletedExplicitFormulaCorrectionLeftOnePoleVerticalIntegral
                    f F (h.height_schedule.height u) - A)))
            hbound
            hmajorant)

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
