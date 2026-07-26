import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.FiniteRectangleResidues.OwnerParts.Part32

/-!
# Finite-rectangle residue error with fixed-degree horizontal growth

This file owns the final Part32 residue-error wrapper that uses fixed-degree
scheduled horizontal log-derivative growth.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open Complex
open Filter
open MeasureTheory
open scoped Topology

namespace ZetaAdmissibleFunction

/-- Core finite-rectangle residue-calculus error theorem with fixed-degree
scheduled horizontal decay. -/
theorem explicitFormulaFamilyResidueWindowError_tendsto_zero_of_polynomialScheduledPackage_core_ownerResidueCalculus
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (hPoly : ExplicitFormulaScheduledPolynomialFamilyAnalyticPackage f F)
    (hschedule : hPoly.height_schedule = h.height_schedule)
    (hfinite :
      ∀ u : ℝ,
        zetaCompletedExplicitFormulaContourIntegral f
            (F.rectangle (h.height_schedule.height u)) =
          explicitFormulaCompletedZeroContourHeightWindowResidueSum f
            (h.height_schedule.height u)) :
    Tendsto
      (fun u : ℝ =>
        explicitFormulaFamilyResidueWindowError f F
          (h.height_schedule.height u))
      atTop
      (𝓝 0) := by
  have hvertical :
      Tendsto
        (fun u : ℝ =>
          explicitFormulaFamilyVerticalResidueWindowError f F
            (h.height_schedule.height u))
        atTop
        (𝓝 0) :=
    explicitFormulaFamilyVerticalResidueWindowError_tendsto_zero_of_polynomialScheduledPackage_ownerFiniteRectangleResidueTheorem
      f F h hPoly hschedule hfinite
  have hhorizontalPoly :
      Tendsto
        (fun u : ℝ =>
          explicitFormulaFamilyHorizontalResidueWindowError f F
            (hPoly.height_schedule.height u))
        atTop
        (𝓝 0) :=
    explicitFormulaFamilyHorizontalResidueWindowError_tendsto_zero_of_polynomialScheduledPackage
      f F hPoly
  have hscheduleFunction :
      (fun u : ℝ =>
          explicitFormulaFamilyHorizontalResidueWindowError f F
            (hPoly.height_schedule.height u)) =
        (fun u : ℝ =>
          explicitFormulaFamilyHorizontalResidueWindowError f F
            (h.height_schedule.height u)) :=
    congrArg
      (fun schedule : ExplicitFormulaCofinalHeightSchedule F =>
        fun u : ℝ =>
          explicitFormulaFamilyHorizontalResidueWindowError f F
            (schedule.height u))
      hschedule
  have hhorizontal :
      Tendsto
        (fun u : ℝ =>
          explicitFormulaFamilyHorizontalResidueWindowError f F
            (h.height_schedule.height u))
        atTop
        (𝓝 0) :=
    Eq.subst
      (motive := fun φ : ℝ → ℂ => Tendsto φ atTop (𝓝 0))
      hscheduleFunction
      hhorizontalPoly
  have hsum :
      Tendsto
        (fun u : ℝ =>
          explicitFormulaFamilyVerticalResidueWindowError f F
              (h.height_schedule.height u) +
            explicitFormulaFamilyHorizontalResidueWindowError f F
              (h.height_schedule.height u))
        atTop
        (𝓝 (0 + 0 : ℂ)) :=
    hvertical.add hhorizontal
  have htarget : (0 + 0 : ℂ) = 0 :=
    add_zero 0
  have hpointwise :
      (fun u : ℝ =>
        explicitFormulaFamilyResidueWindowError f F
          (h.height_schedule.height u)) =
        (fun u : ℝ =>
          explicitFormulaFamilyVerticalResidueWindowError f F
              (h.height_schedule.height u) +
            explicitFormulaFamilyHorizontalResidueWindowError f F
              (h.height_schedule.height u)) := by
    exact funext
      (fun u : ℝ =>
        explicitFormulaFamilyResidueWindowError_eq_vertical_add_horizontal
          f F (h.height_schedule.height u))
  exact Eq.subst
    (motive := fun φ : ℝ → ℂ => Tendsto φ atTop (𝓝 0))
    hpointwise.symm
    (Eq.subst
      (motive := fun z : ℂ =>
        Tendsto
          (fun u : ℝ =>
            explicitFormulaFamilyVerticalResidueWindowError f F
                (h.height_schedule.height u) +
              explicitFormulaFamilyHorizontalResidueWindowError f F
                (h.height_schedule.height u))
          atTop
          (𝓝 z))
      htarget
      hsum)

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
