import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.CorrectionPoleSides

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

/-- The scheduled horizontal remainder for the `s = 0` single-pole rectangle. -/
noncomputable def zetaCompletedExplicitFormulaCorrectionZeroPoleScheduledHorizontalDifference
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) : ℂ :=
  zetaCompletedExplicitFormulaCorrectionTopZeroPoleHorizontalIntegral
      f F (h.height_schedule.height u) -
    zetaCompletedExplicitFormulaCorrectionBottomZeroPoleHorizontalIntegral
      f F (h.height_schedule.height u)

/-- The scheduled horizontal remainder for the `s = 1` single-pole rectangle. -/
noncomputable def zetaCompletedExplicitFormulaCorrectionOnePoleScheduledHorizontalDifference
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) : ℂ :=
  zetaCompletedExplicitFormulaCorrectionTopOnePoleHorizontalIntegral
      f F (h.height_schedule.height u) -
    zetaCompletedExplicitFormulaCorrectionBottomOnePoleHorizontalIntegral
      f F (h.height_schedule.height u)

/-- The scheduled `s = 0` horizontal single-pole remainder unfolds to its
top-minus-bottom definition. -/
theorem zetaCompletedExplicitFormulaCorrectionZeroPoleScheduledHorizontalDifference_eq
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    zetaCompletedExplicitFormulaCorrectionZeroPoleScheduledHorizontalDifference f F h u =
      zetaCompletedExplicitFormulaCorrectionTopZeroPoleHorizontalIntegral
          f F (h.height_schedule.height u) -
        zetaCompletedExplicitFormulaCorrectionBottomZeroPoleHorizontalIntegral
          f F (h.height_schedule.height u) :=
  rfl

/-- The scheduled `s = 1` horizontal single-pole remainder unfolds to its
top-minus-bottom definition. -/
theorem zetaCompletedExplicitFormulaCorrectionOnePoleScheduledHorizontalDifference_eq
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    zetaCompletedExplicitFormulaCorrectionOnePoleScheduledHorizontalDifference f F h u =
      zetaCompletedExplicitFormulaCorrectionTopOnePoleHorizontalIntegral
          f F (h.height_schedule.height u) -
        zetaCompletedExplicitFormulaCorrectionBottomOnePoleHorizontalIntegral
          f F (h.height_schedule.height u) :=
  rfl

/-- The isolated scheduled `s = 0` horizontal remainder is bounded by the two
single-pole horizontal edges. -/
theorem zetaCompletedExplicitFormulaCorrectionZeroPoleScheduledHorizontalDifference_norm_le_edges
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    ‖zetaCompletedExplicitFormulaCorrectionZeroPoleScheduledHorizontalDifference f F h u‖
      ≤
        ‖zetaCompletedExplicitFormulaCorrectionTopZeroPoleHorizontalIntegral
          f F (h.height_schedule.height u)‖ +
        ‖zetaCompletedExplicitFormulaCorrectionBottomZeroPoleHorizontalIntegral
          f F (h.height_schedule.height u)‖ := by
  let U : ℂ :=
    zetaCompletedExplicitFormulaCorrectionTopZeroPoleHorizontalIntegral
      f F (h.height_schedule.height u)
  let B : ℂ :=
    zetaCompletedExplicitFormulaCorrectionBottomZeroPoleHorizontalIntegral
      f F (h.height_schedule.height u)
  change ‖U - B‖ ≤ ‖U‖ + ‖B‖
  exact norm_sub_le U B

/-- The isolated scheduled `s = 1` horizontal remainder is bounded by the two
single-pole horizontal edges. -/
theorem zetaCompletedExplicitFormulaCorrectionOnePoleScheduledHorizontalDifference_norm_le_edges
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    ‖zetaCompletedExplicitFormulaCorrectionOnePoleScheduledHorizontalDifference f F h u‖
      ≤
        ‖zetaCompletedExplicitFormulaCorrectionTopOnePoleHorizontalIntegral
          f F (h.height_schedule.height u)‖ +
        ‖zetaCompletedExplicitFormulaCorrectionBottomOnePoleHorizontalIntegral
          f F (h.height_schedule.height u)‖ := by
  let U : ℂ :=
    zetaCompletedExplicitFormulaCorrectionTopOnePoleHorizontalIntegral
      f F (h.height_schedule.height u)
  let B : ℂ :=
    zetaCompletedExplicitFormulaCorrectionBottomOnePoleHorizontalIntegral
      f F (h.height_schedule.height u)
  change ‖U - B‖ ≤ ‖U‖ + ‖B‖
  exact norm_sub_le U B

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
