import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaZeroKreinGram.WeilCriterion.OwnerParts.PolynomialPhysicalBoundaryTransportsParts.ProjectContour

/-!
# Polynomial scheduled project-contour transport with supplied horizontal decay

This file separates the horizontal-decay input from the polynomial scheduled
vertical zero-side endpoint.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open Filter
open scoped Topology

namespace ZetaAdmissibleFunction

/-- A polynomial scheduled normalized project-contour zero-side limit and an
explicit horizontal-side limit give the polynomial scheduled vertical zero-side
endpoint. -/
theorem explicitFormulaPolynomialScheduledPackageNormalizedPoleCorrectedVerticalDifference_tendsto_zeroSideComplex_of_projectContourLimit_horizontal
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaScheduledPolynomialFamilyAnalyticPackage f F)
    (projectLimit :
      Tendsto
        (fun u : ℝ =>
          explicitFormulaRectangleNormalizedPoleCorrectedContourIntegral
            f F (h.height_schedule.height u))
        atTop
        (𝓝 (zetaCompletedZeroSideComplex f)))
    (horizontalLimit :
      Tendsto
        (fun u : ℝ =>
          explicitFormulaPolynomialScheduledPackageHorizontalSideDifference h u)
        atTop
        (𝓝 (0 : ℂ))) :
    Tendsto
      (fun u : ℝ =>
        (zetaCompletedExplicitFormulaRightLineIntegral f
              (F.rectangle (h.height_schedule.height u)) -
            zetaCompletedExplicitFormulaLeftLineIntegral f
              (F.rectangle (h.height_schedule.height u))) /
            explicitFormulaTwoPi -
          explicitFormulaRectangle_completedPoleResidueSum f)
      atTop
      (𝓝 (zetaCompletedZeroSideComplex f)) :=
  let normalizedHorizontalLimit :
      Tendsto
        (fun u : ℝ =>
          explicitFormulaPolynomialScheduledPackageHorizontalSideDifference h u /
            explicitFormulaTwoPi)
        atTop
        (𝓝 ((0 : ℂ) / explicitFormulaTwoPi)) :=
    horizontalLimit.div_const explicitFormulaTwoPi
  let differenceLimit :
      Tendsto
        (fun u : ℝ =>
          explicitFormulaRectangleNormalizedPoleCorrectedContourIntegral
              f F (h.height_schedule.height u) -
            explicitFormulaPolynomialScheduledPackageHorizontalSideDifference h u /
              explicitFormulaTwoPi)
        atTop
        (𝓝 (zetaCompletedZeroSideComplex f - (0 : ℂ) / explicitFormulaTwoPi)) :=
    projectLimit.sub normalizedHorizontalLimit
  let zeroDivision :
      (0 : ℂ) / explicitFormulaTwoPi = 0 :=
    zero_div explicitFormulaTwoPi
  let targetEquality :
      zetaCompletedZeroSideComplex f - (0 : ℂ) / explicitFormulaTwoPi =
        zetaCompletedZeroSideComplex f :=
    Eq.trans
      (congrArg
        (fun term : ℂ => zetaCompletedZeroSideComplex f - term)
        zeroDivision)
      (sub_zero (zetaCompletedZeroSideComplex f))
  let functionEquality :
      (fun u : ℝ =>
        explicitFormulaRectangleNormalizedPoleCorrectedContourIntegral
            f F (h.height_schedule.height u) -
          explicitFormulaPolynomialScheduledPackageHorizontalSideDifference h u /
            explicitFormulaTwoPi) =
      (fun u : ℝ =>
        (zetaCompletedExplicitFormulaRightLineIntegral f
              (F.rectangle (h.height_schedule.height u)) -
            zetaCompletedExplicitFormulaLeftLineIntegral f
              (F.rectangle (h.height_schedule.height u))) /
            explicitFormulaTwoPi -
          explicitFormulaRectangle_completedPoleResidueSum f) :=
    funext
      (fun u : ℝ =>
        (explicitFormulaPolynomialScheduledPackageNormalizedPoleCorrectedVerticalDifference_eq_contour_sub_horizontal
          f F h u).symm)
  Eq.subst
    (motive := fun values : ℝ → ℂ =>
      Tendsto values atTop (𝓝 (zetaCompletedZeroSideComplex f)))
    functionEquality
    (Eq.subst
      (motive := fun target : ℂ =>
        Tendsto
          (fun u : ℝ =>
            explicitFormulaRectangleNormalizedPoleCorrectedContourIntegral
                f F (h.height_schedule.height u) -
              explicitFormulaPolynomialScheduledPackageHorizontalSideDifference h u /
                explicitFormulaTwoPi)
          atTop
          (𝓝 target))
      targetEquality
      differenceLimit)

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
