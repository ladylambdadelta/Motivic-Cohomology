import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.HorizontalDecay.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.FiniteRectangleResidues.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.VerticalChannels.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ContourAssembly.Owner

/-!
# Boundary explicit-formula complex analysis owner re-export

This compatibility owner re-exports the horizontal-decay, finite-rectangle residue,
vertical-channel, and contour-assembly owner layers without changing public theorem names.
-/

namespace Boundary
namespace LFunctions

noncomputable section

namespace ZetaAdmissibleFunction

/-- Exact normalization bridge between the finite vertical-window error and the
scheduled normalized pole-corrected vertical packet.  The final parenthesized term
is the explicit pole/window normalization defect; it is retained rather than silently
identified with zero. -/
theorem explicitFormulaFamilyVerticalResidueWindowError_eq_twoPi_smul_scheduledNormalizedVerticalDifference_add_normalizationDefect
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaScheduledFamilyAnalyticPackage f F) (u : ℝ) :
    explicitFormulaFamilyVerticalResidueWindowError f F
        (h.height_schedule.height u) =
      explicitFormulaTwoPi *
          explicitFormulaScheduledPackageNormalizedPoleCorrectedVerticalDifference
            f F h u +
        (explicitFormulaTwoPi * explicitFormulaRectangle_completedPoleResidueSum f -
          explicitFormulaCompletedZeroContourHeightWindowResidueSum f
            (h.height_schedule.height u)) := by
  let vertical : ℂ :=
    zetaCompletedExplicitFormulaRightLineIntegral f
        (F.rectangle (h.height_schedule.height u)) -
      zetaCompletedExplicitFormulaLeftLineIntegral f
        (F.rectangle (h.height_schedule.height u))
  let poles : ℂ := explicitFormulaRectangle_completedPoleResidueSum f
  let window : ℂ :=
    explicitFormulaCompletedZeroContourHeightWindowResidueSum f
      (h.height_schedule.height u)
  have hscaled :
      explicitFormulaTwoPi *
          explicitFormulaScheduledPackageNormalizedPoleCorrectedVerticalDifference
            f F h u =
        vertical - explicitFormulaTwoPi * poles := by
    change explicitFormulaTwoPi * (vertical / explicitFormulaTwoPi - poles) =
      vertical - explicitFormulaTwoPi * poles
    calc
      explicitFormulaTwoPi * (vertical / explicitFormulaTwoPi - poles) =
          explicitFormulaTwoPi * (vertical / explicitFormulaTwoPi) -
            explicitFormulaTwoPi * poles :=
        mul_sub explicitFormulaTwoPi (vertical / explicitFormulaTwoPi) poles
      _ = vertical - explicitFormulaTwoPi * poles := by
        exact congrArg
          (fun value : ℂ => value - explicitFormulaTwoPi * poles)
          (mul_div_cancel₀ vertical explicitFormulaTwoPi_ne_zero)
  change vertical - window =
    explicitFormulaTwoPi *
          explicitFormulaScheduledPackageNormalizedPoleCorrectedVerticalDifference
            f F h u +
        (explicitFormulaTwoPi * poles - window)
  calc
    vertical - window =
        (vertical - explicitFormulaTwoPi * poles) +
          (explicitFormulaTwoPi * poles - window) :=
      (sub_add_sub_cancel vertical (explicitFormulaTwoPi * poles) window).symm
    _ = explicitFormulaTwoPi *
          explicitFormulaScheduledPackageNormalizedPoleCorrectedVerticalDifference
            f F h u +
        (explicitFormulaTwoPi * poles - window) :=
      congrArg
        (fun value : ℂ => value + (explicitFormulaTwoPi * poles - window))
        hscaled.symm

/-- Transport a scheduled normalized vertical limit to the finite vertical-window
error once the separately identified pole/window normalization defect is known to
vanish.  The defect is not expected to vanish by residue bookkeeping alone: the
two pole residues are the explicit values of the test transform at `-1/2` and `1/2`.
This theorem therefore records a genuine normalization obligation, not a shortcut
around the normalized contour route. -/
theorem explicitFormulaFamilyVerticalResidueWindowError_tendsto_zero_of_scheduledNormalizedVerticalDifference_and_normalizationDefect
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaScheduledFamilyAnalyticPackage f F)
    (hvertical :
      Tendsto
        (fun u : ℝ =>
          explicitFormulaScheduledPackageNormalizedPoleCorrectedVerticalDifference
            f F h u)
        atTop
        (𝓝 0))
    (hdefect :
      Tendsto
        (fun u : ℝ =>
          explicitFormulaTwoPi * explicitFormulaRectangle_completedPoleResidueSum f -
            explicitFormulaCompletedZeroContourHeightWindowResidueSum f
              (h.height_schedule.height u))
        atTop
        (𝓝 0)) :
    Tendsto
      (fun u : ℝ =>
        explicitFormulaFamilyVerticalResidueWindowError f F
          (h.height_schedule.height u))
      atTop
      (𝓝 0) := by
  have hscaled :
      Tendsto
        (fun u : ℝ =>
          explicitFormulaTwoPi *
            explicitFormulaScheduledPackageNormalizedPoleCorrectedVerticalDifference
              f F h u)
        atTop
        (𝓝 (explicitFormulaTwoPi * 0)) :=
    hvertical.const_mul explicitFormulaTwoPi
  have hsum :
      Tendsto
        (fun u : ℝ =>
          explicitFormulaTwoPi *
              explicitFormulaScheduledPackageNormalizedPoleCorrectedVerticalDifference
                f F h u +
            (explicitFormulaTwoPi * explicitFormulaRectangle_completedPoleResidueSum f -
              explicitFormulaCompletedZeroContourHeightWindowResidueSum f
                (h.height_schedule.height u)))
        atTop
        (𝓝 (explicitFormulaTwoPi * 0 + 0)) :=
    hscaled.add hdefect
  have htarget : explicitFormulaTwoPi * 0 + 0 = 0 := by
    exact add_zero (mul_zero explicitFormulaTwoPi)
  have hpointwise :
      (fun u : ℝ =>
        explicitFormulaFamilyVerticalResidueWindowError f F
          (h.height_schedule.height u)) =
        (fun u : ℝ =>
          explicitFormulaTwoPi *
              explicitFormulaScheduledPackageNormalizedPoleCorrectedVerticalDifference
                f F h u +
            (explicitFormulaTwoPi * explicitFormulaRectangle_completedPoleResidueSum f -
              explicitFormulaCompletedZeroContourHeightWindowResidueSum f
                (h.height_schedule.height u))) := by
    exact funext
      (fun u : ℝ =>
        explicitFormulaFamilyVerticalResidueWindowError_eq_twoPi_smul_scheduledNormalizedVerticalDifference_add_normalizationDefect
          f F h u)
  exact Eq.subst
    (motive := fun φ : ℝ → ℂ => Tendsto φ atTop (𝓝 0))
    hpointwise.symm
    (Eq.subst
      (motive := fun z : ℂ =>
        Tendsto
          (fun u : ℝ =>
            explicitFormulaTwoPi *
                explicitFormulaScheduledPackageNormalizedPoleCorrectedVerticalDifference
                  f F h u +
              (explicitFormulaTwoPi * explicitFormulaRectangle_completedPoleResidueSum f -
                explicitFormulaCompletedZeroContourHeightWindowResidueSum f
                  (h.height_schedule.height u)))
          atTop
          (𝓝 z))
      htarget
      hsum)

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
