import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.ScheduledNormalizedContourResidueLimit

/-!
# Scheduled normalized contour residue with supplied horizontal decay

This owner part isolates the horizontal-decay input needed to pass from the
normalized full contour limit to the normalized vertical-channel limit.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open Filter
open scoped Topology

namespace ZetaAdmissibleFunction

/-- The scheduled-package normalized vertical side converges to the completed
zero side from explicit horizontal decay and eventual selected tangent-residue
equality. -/
theorem explicitFormulaScheduledPackageNormalizedPoleCorrectedVerticalDifference_tendsto_zeroSideComplex_of_horizontal
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaScheduledFamilyAnalyticPackage f F)
    (htangentEventual :
      ∀ᶠ u in atTop,
        explicitFormulaRectangle_poleCorrectedResidueSum f
            (h.height_schedule.height u) =
          zetaCompletedExplicitFormulaNormalizedTangentContourIntegral f
            (F.rectangle (h.height_schedule.height u)))
    (hhorizontal :
      Tendsto
        (fun u : ℝ => explicitFormulaScheduledPackageHorizontalSideDifference h u)
        atTop (𝓝 0))
    (hsum :
      Summable
        (fun rho : {rho : ℂ // ZetaCompletedZero rho} =>
          zetaZeroSideContribution (rho : ℂ) f)) :
    Tendsto
      (fun u : ℝ =>
        explicitFormulaScheduledPackageNormalizedPoleCorrectedVerticalDifference
          f F h u)
      atTop (𝓝 (zetaCompletedZeroSideComplex f)) :=
  let hcontour :
      Tendsto
        (fun u : ℝ =>
          explicitFormulaRectangleNormalizedPoleCorrectedContourIntegral
            f F (h.height_schedule.height u))
        atTop (𝓝 (zetaCompletedZeroSideComplex f)) :=
    explicitFormulaRectangleNormalizedPoleCorrectedContourIntegral_tendsto_zeroSideComplex_of_scheduledPackage
      f F h htangentEventual hsum
  let hnormalizedHorizontal :
      Tendsto
        (fun u : ℝ =>
          explicitFormulaScheduledPackageHorizontalSideDifference h u /
            explicitFormulaTwoPi)
        atTop (𝓝 (0 / explicitFormulaTwoPi : ℂ)) :=
    hhorizontal.div_const explicitFormulaTwoPi
  let hdifference :
      Tendsto
        (fun u : ℝ =>
          explicitFormulaRectangleNormalizedPoleCorrectedContourIntegral
              f F (h.height_schedule.height u) -
            explicitFormulaScheduledPackageHorizontalSideDifference h u /
              explicitFormulaTwoPi)
        atTop
        (𝓝
          (zetaCompletedZeroSideComplex f -
            (0 / explicitFormulaTwoPi : ℂ))) :=
    hcontour.sub hnormalizedHorizontal
  let hzeroDiv :
      (0 : ℂ) / explicitFormulaTwoPi = 0 :=
    zero_div explicitFormulaTwoPi
  let htarget :
      zetaCompletedZeroSideComplex f -
          (0 / explicitFormulaTwoPi : ℂ) =
        zetaCompletedZeroSideComplex f :=
    Eq.trans
      (congrArg
        (fun term : ℂ => zetaCompletedZeroSideComplex f - term)
        hzeroDiv)
      (sub_zero (zetaCompletedZeroSideComplex f))
  let hpointwise :
      (fun u : ℝ =>
        explicitFormulaRectangleNormalizedPoleCorrectedContourIntegral
            f F (h.height_schedule.height u) -
          explicitFormulaScheduledPackageHorizontalSideDifference h u /
            explicitFormulaTwoPi) =
        (fun u : ℝ =>
          explicitFormulaScheduledPackageNormalizedPoleCorrectedVerticalDifference
            f F h u) :=
    funext
      (fun u : ℝ =>
        (explicitFormulaScheduledPackageNormalizedPoleCorrectedVerticalDifference_eq_contour_sub_horizontal
          f F h u).symm)
  Eq.subst
    (motive := fun values : ℝ → ℂ =>
      Tendsto values atTop (𝓝 (zetaCompletedZeroSideComplex f)))
    hpointwise
    (Eq.subst
      (motive := fun target : ℂ =>
        Tendsto
          (fun u : ℝ =>
            explicitFormulaRectangleNormalizedPoleCorrectedContourIntegral
                f F (h.height_schedule.height u) -
              explicitFormulaScheduledPackageHorizontalSideDifference h u /
                explicitFormulaTwoPi)
          atTop (𝓝 target))
      htarget hdifference)

theorem explicitFormulaScheduledPackageNormalizedPoleCorrectedVerticalDifference_tendsto_zeroSideComplex_of_canonicalResidue_and_horizontal_owner
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaScheduledFamilyAnalyticPackage f F)
    (hhorizontal :
      Tendsto
        (fun u : ℝ =>
          explicitFormulaScheduledPackageHorizontalSideDifference h u)
        atTop (𝓝 0))
    (hsum :
      Summable
        (fun rho : {rho : ℂ // ZetaCompletedZero rho} =>
          zetaZeroSideContribution (rho : ℂ) f)) :
    Tendsto
      (fun u : ℝ =>
        explicitFormulaScheduledPackageNormalizedPoleCorrectedVerticalDifference
          f F h u)
      atTop (𝓝 (zetaCompletedZeroSideComplex f)) :=
  explicitFormulaScheduledPackageNormalizedPoleCorrectedVerticalDifference_tendsto_zeroSideComplex_of_horizontal
    f F h
    (explicitFormulaScheduledPackage_poleCorrectedResidueSum_eq_normalizedTangentContourIntegral_eventually_canonical_owner
      f F h)
    hhorizontal
    hsum

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
