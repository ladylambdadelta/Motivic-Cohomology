import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ContourAssembly.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaZeroKreinGram.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaCompletedHilbertSource.Owner

/-!
# Upstream positivity bridge for the final RH wrapper

This file owns the analytic bridge from the completed explicit formula on
autocorrelation probes to the nonnegative boundary/GNS realization.  The final
RH wrapper consumes `zetaWeilQuadraticPositivity_ownerGap`; the proof here is a
thin transport from contour assembly to the positive boundary realization, with
the prime finite-window reconstruction datum left explicit.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped Topology

/-- Owner theorem: packaged contour-shift equality from the completed Weil form on an
autocorrelation to the completed explicit-formula boundary channel. -/
theorem zetaWeilFormCompleted_convolutionAutocorrelation_eq_completedBoundaryChannel_re_ownerGap
    (f : ZetaAdmissibleFunction)
    (schedule :
      ZetaAdmissibleFunction.ExplicitFormulaHorizontalAvoidingHeightSchedule
        (ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_contourFamily f))
    (hPhi : ZetaPhiAnalyticControl
      (ZetaAdmissibleFunction.convolutionAutocorrelation f))
    (hLog : CompletedZetaNegLogDerivControl
      (ZetaAdmissibleFunction.convolutionAutocorrelation f))
    (hcontourScheduled :
      Tendsto
        (fun u : ℝ =>
          ZetaAdmissibleFunction.zetaCompletedExplicitFormulaContourIntegral
            (ZetaAdmissibleFunction.convolutionAutocorrelation f)
            ((ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_contourFamily f).rectangle
              ((ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_familyAnalyticPackage
                f schedule hPhi hLog).height_schedule.height u)))
        atTop
        (𝓝 (ZetaAdmissibleFunction.zetaCompletedZeroSideComplex
          (ZetaAdmissibleFunction.convolutionAutocorrelation f))))
    (E : CompletedZetaZeroExcisedStrip
      (min (ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c
        (1 - (ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c))
      (max (ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c
        (1 - (ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c)))
    (hTopMem :
      ∀ (u x : ℝ),
        x ∈ Set.uIcc
          (ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c
          (1 - (ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c) →
        ZetaAdmissibleFunction.zetaCompletedExplicitFormulaTopPath
          ((ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_contourFamily f).rectangle
            ((ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_familyAnalyticPackage
              f schedule hPhi hLog).height_schedule.height u)) x ∈ E.carrier)
    (hBottomMem :
      ∀ (u x : ℝ),
        x ∈ Set.uIcc
          (ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c
          (1 - (ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c) →
        ZetaAdmissibleFunction.zetaCompletedExplicitFormulaBottomPath
          ((ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_contourFamily f).rectangle
            ((ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_familyAnalyticPackage
              f schedule hPhi hLog).height_schedule.height u)) x ∈ E.carrier) :
    zetaWeilFormCompleted
        (ZetaAdmissibleFunction.convolutionAutocorrelation f) =
      Complex.re
        (ZetaAdmissibleFunction.completedBoundaryChannel
          (ZetaAdmissibleFunction.convolutionAutocorrelation f)) := by
  exact
    ZetaAdmissibleFunction.zetaWeilFormCompleted_convolutionAutocorrelation_eq_completedBoundaryChannel_re_of_scheduledHorizontalCarrier_ownerContourAssembly
      f schedule hPhi hLog hcontourScheduled E hTopMem hBottomMem

/-- Upstream owner theorem: completed Weil quadratic positivity on autocorrelation probes,
assembled from the contour-shift bridge, the prime finite-window reconstruction, and the
positive boundary/GNS realization. -/
theorem zetaWeilQuadraticPositivity_ownerGap
    (hschedule :
      ∀ f : ZetaAdmissibleFunction,
        ZetaAdmissibleFunction.ExplicitFormulaHorizontalAvoidingHeightSchedule
          (ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_contourFamily f))
    (hPhi :
      ∀ f : ZetaAdmissibleFunction,
        ZetaPhiAnalyticControl
          (ZetaAdmissibleFunction.convolutionAutocorrelation f))
    (hLog :
      ∀ f : ZetaAdmissibleFunction,
        CompletedZetaNegLogDerivControl
          (ZetaAdmissibleFunction.convolutionAutocorrelation f))
    (hcontourScheduled :
      ∀ f : ZetaAdmissibleFunction,
        Tendsto
          (fun u : ℝ =>
            ZetaAdmissibleFunction.zetaCompletedExplicitFormulaContourIntegral
              (ZetaAdmissibleFunction.convolutionAutocorrelation f)
              ((ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_contourFamily f).rectangle
                ((ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_familyAnalyticPackage
                  f (hschedule f) (hPhi f) (hLog f)).height_schedule.height u)))
          atTop
          (𝓝 (ZetaAdmissibleFunction.zetaCompletedZeroSideComplex
            (ZetaAdmissibleFunction.convolutionAutocorrelation f))))
    (E :
      ∀ f : ZetaAdmissibleFunction,
        CompletedZetaZeroExcisedStrip
          (min (ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c
            (1 - (ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c))
          (max (ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c
            (1 - (ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c)))
    (hTopMem :
      ∀ f : ZetaAdmissibleFunction,
        ∀ (u x : ℝ),
          x ∈ Set.uIcc
            (ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c
            (1 - (ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c) →
          ZetaAdmissibleFunction.zetaCompletedExplicitFormulaTopPath
            ((ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_contourFamily f).rectangle
              ((ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_familyAnalyticPackage
                f (hschedule f) (hPhi f) (hLog f)).height_schedule.height u)) x ∈ (E f).carrier)
    (hBottomMem :
      ∀ f : ZetaAdmissibleFunction,
        ∀ (u x : ℝ),
          x ∈ Set.uIcc
            (ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c
            (1 - (ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c) →
          ZetaAdmissibleFunction.zetaCompletedExplicitFormulaBottomPath
            ((ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_contourFamily f).rectangle
              ((ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_familyAnalyticPackage
                f (hschedule f) (hPhi f) (hLog f)).height_schedule.height u)) x ∈ (E f).carrier)
    (hPrime :
      ∀ f : ZetaAdmissibleFunction,
        ZetaAdmissibleFunction.CompletedFiniteWindowPrimeDistributionReconstruction f) :
    ZetaWeilQuadraticPositivity := by
  exact
    fun f =>
      have hbridge :
          zetaWeilFormCompleted
              (ZetaAdmissibleFunction.convolutionAutocorrelation f) =
            Complex.re
        (ZetaAdmissibleFunction.completedBoundaryChannel
          (ZetaAdmissibleFunction.convolutionAutocorrelation f)) :=
        zetaWeilFormCompleted_convolutionAutocorrelation_eq_completedBoundaryChannel_re_ownerGap
          f (hschedule f) (hPhi f) (hLog f) (hcontourScheduled f) (E f) (hTopMem f) (hBottomMem f)
      Eq.subst
        (motive := fun x : ℝ => 0 ≤ x)
        hbridge.symm
        (ZetaAdmissibleFunction.completedBoundaryChannel_convolutionAutocorrelation_re_nonnegative_ownerGap
          f (hPrime f))

/-- Owner theorem: packaged contour-shift equality from the completed Weil form on an
autocorrelation to the completed explicit-formula boundary channel, using the scheduled
horizontal carrier constructed by the analytic package. -/
theorem zetaWeilFormCompleted_convolutionAutocorrelation_eq_completedBoundaryChannel_re_constructedScheduledCarrier
    (f : ZetaAdmissibleFunction)
    (schedule :
      ZetaAdmissibleFunction.ExplicitFormulaHorizontalAvoidingHeightSchedule
        (ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_contourFamily f))
    (hPhi : ZetaPhiAnalyticControl
      (ZetaAdmissibleFunction.convolutionAutocorrelation f))
    (hLog : CompletedZetaNegLogDerivControl
      (ZetaAdmissibleFunction.convolutionAutocorrelation f))
    (hcontourScheduled :
      Tendsto
        (fun u : ℝ =>
          ZetaAdmissibleFunction.zetaCompletedExplicitFormulaContourIntegral
            (ZetaAdmissibleFunction.convolutionAutocorrelation f)
            ((ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_contourFamily f).rectangle
              ((ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_familyAnalyticPackage
                f schedule hPhi hLog).height_schedule.height u)))
        atTop
        (𝓝 (ZetaAdmissibleFunction.zetaCompletedZeroSideComplex
          (ZetaAdmissibleFunction.convolutionAutocorrelation f)))) :
    zetaWeilFormCompleted
        (ZetaAdmissibleFunction.convolutionAutocorrelation f) =
      Complex.re
        (ZetaAdmissibleFunction.completedBoundaryChannel
          (ZetaAdmissibleFunction.convolutionAutocorrelation f)) := by
  exact
    ZetaAdmissibleFunction.zetaWeilFormCompleted_convolutionAutocorrelation_eq_completedBoundaryChannel_re_of_constructedScheduledHorizontalCarrier_ownerContourAssembly
      f schedule hPhi hLog hcontourScheduled

/-- Owner theorem: packaged contour-shift equality using constructed scheduled
horizontal carrier and the finite-rectangle residue-calculus contour limit. -/
theorem zetaWeilFormCompleted_convolutionAutocorrelation_eq_completedBoundaryChannel_re_constructedScheduledContour
    (f : ZetaAdmissibleFunction)
    (schedule :
      ZetaAdmissibleFunction.ExplicitFormulaHorizontalAvoidingHeightSchedule
        (ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_contourFamily f))
    (hPhi : ZetaPhiAnalyticControl
      (ZetaAdmissibleFunction.convolutionAutocorrelation f))
    (hLog : CompletedZetaNegLogDerivControl
      (ZetaAdmissibleFunction.convolutionAutocorrelation f))
    (N : ℕ)
    (hfinite :
      ∀ u : ℝ,
        ZetaAdmissibleFunction.zetaCompletedExplicitFormulaContourIntegral
            (ZetaAdmissibleFunction.convolutionAutocorrelation f)
            ((ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_contourFamily f).rectangle
              ((ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_familyAnalyticPackage
                f schedule hPhi hLog).height_schedule.height u)) =
          ZetaAdmissibleFunction.explicitFormulaCompletedZeroHeightWindowResidueSum
            (ZetaAdmissibleFunction.convolutionAutocorrelation f)
            ((ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_familyAnalyticPackage
              f schedule hPhi hLog).height_schedule.height u))
    (hsum :
      Summable
        (fun ρ : {ρ : ℂ // ZetaCompletedZero ρ} =>
          zetaZeroSideContribution (ρ : ℂ)
            (ZetaAdmissibleFunction.convolutionAutocorrelation f))) :
    zetaWeilFormCompleted
        (ZetaAdmissibleFunction.convolutionAutocorrelation f) =
      Complex.re
        (ZetaAdmissibleFunction.completedBoundaryChannel
          (ZetaAdmissibleFunction.convolutionAutocorrelation f)) := by
  exact
    ZetaAdmissibleFunction.zetaWeilFormCompleted_convolutionAutocorrelation_eq_completedBoundaryChannel_re_of_constructedScheduledContour_ownerContourAssembly
      f schedule hPhi hLog N hfinite hsum

/-- Upstream owner theorem: completed Weil quadratic positivity on autocorrelation probes,
using the scheduled horizontal carrier constructed by the analytic package. -/
theorem zetaWeilQuadraticPositivity_of_constructedScheduledCarrier
    (hschedule :
      ∀ f : ZetaAdmissibleFunction,
        ZetaAdmissibleFunction.ExplicitFormulaHorizontalAvoidingHeightSchedule
          (ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_contourFamily f))
    (hPhi :
      ∀ f : ZetaAdmissibleFunction,
        ZetaPhiAnalyticControl
          (ZetaAdmissibleFunction.convolutionAutocorrelation f))
    (hLog :
      ∀ f : ZetaAdmissibleFunction,
        CompletedZetaNegLogDerivControl
          (ZetaAdmissibleFunction.convolutionAutocorrelation f))
    (hcontourScheduled :
      ∀ f : ZetaAdmissibleFunction,
        Tendsto
          (fun u : ℝ =>
            ZetaAdmissibleFunction.zetaCompletedExplicitFormulaContourIntegral
              (ZetaAdmissibleFunction.convolutionAutocorrelation f)
              ((ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_contourFamily f).rectangle
                ((ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_familyAnalyticPackage
                  f (hschedule f) (hPhi f) (hLog f)).height_schedule.height u)))
          atTop
          (𝓝 (ZetaAdmissibleFunction.zetaCompletedZeroSideComplex
            (ZetaAdmissibleFunction.convolutionAutocorrelation f))))
    (hPrime :
      ∀ f : ZetaAdmissibleFunction,
        ZetaAdmissibleFunction.CompletedFiniteWindowPrimeDistributionReconstruction f) :
    ZetaWeilQuadraticPositivity := by
  exact
    fun f =>
      have hbridge :
          zetaWeilFormCompleted
              (ZetaAdmissibleFunction.convolutionAutocorrelation f) =
            Complex.re
              (ZetaAdmissibleFunction.completedBoundaryChannel
                (ZetaAdmissibleFunction.convolutionAutocorrelation f)) :=
        zetaWeilFormCompleted_convolutionAutocorrelation_eq_completedBoundaryChannel_re_constructedScheduledCarrier
          f (hschedule f) (hPhi f) (hLog f) (hcontourScheduled f)
      Eq.subst
        (motive := fun x : ℝ => 0 ≤ x)
        hbridge.symm
        (ZetaAdmissibleFunction.completedBoundaryChannel_convolutionAutocorrelation_re_nonnegative_ownerGap
          f (hPrime f))

/-- Upstream owner theorem: completed Weil quadratic positivity on autocorrelation probes,
using the constructed scheduled horizontal carrier and finite-rectangle residue-calculus
contour limit. -/
theorem zetaWeilQuadraticPositivity_of_constructedScheduledContour
    (hschedule :
      ∀ f : ZetaAdmissibleFunction,
        ZetaAdmissibleFunction.ExplicitFormulaHorizontalAvoidingHeightSchedule
          (ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_contourFamily f))
    (hPhi :
      ∀ f : ZetaAdmissibleFunction,
        ZetaPhiAnalyticControl
          (ZetaAdmissibleFunction.convolutionAutocorrelation f))
    (hLog :
      ∀ f : ZetaAdmissibleFunction,
        CompletedZetaNegLogDerivControl
          (ZetaAdmissibleFunction.convolutionAutocorrelation f))
    (N : ℕ)
    (hfinite :
      ∀ f : ZetaAdmissibleFunction,
        ∀ u : ℝ,
          ZetaAdmissibleFunction.zetaCompletedExplicitFormulaContourIntegral
              (ZetaAdmissibleFunction.convolutionAutocorrelation f)
              ((ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_contourFamily f).rectangle
                ((ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_familyAnalyticPackage
                  f (hschedule f) (hPhi f) (hLog f)).height_schedule.height u)) =
            ZetaAdmissibleFunction.explicitFormulaCompletedZeroHeightWindowResidueSum
              (ZetaAdmissibleFunction.convolutionAutocorrelation f)
              ((ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_familyAnalyticPackage
                f (hschedule f) (hPhi f) (hLog f)).height_schedule.height u))
    (hsum :
      ∀ f : ZetaAdmissibleFunction,
        Summable
          (fun ρ : {ρ : ℂ // ZetaCompletedZero ρ} =>
            zetaZeroSideContribution (ρ : ℂ)
              (ZetaAdmissibleFunction.convolutionAutocorrelation f)))
    (hPrime :
      ∀ f : ZetaAdmissibleFunction,
        ZetaAdmissibleFunction.CompletedFiniteWindowPrimeDistributionReconstruction f) :
    ZetaWeilQuadraticPositivity := by
  exact
    fun f =>
      have hbridge :
          zetaWeilFormCompleted
              (ZetaAdmissibleFunction.convolutionAutocorrelation f) =
            Complex.re
              (ZetaAdmissibleFunction.completedBoundaryChannel
                (ZetaAdmissibleFunction.convolutionAutocorrelation f)) :=
        zetaWeilFormCompleted_convolutionAutocorrelation_eq_completedBoundaryChannel_re_constructedScheduledContour
          f (hschedule f) (hPhi f) (hLog f) N (hfinite f) (hsum f)
      Eq.subst
        (motive := fun x : ℝ => 0 ≤ x)
        hbridge.symm
        (ZetaAdmissibleFunction.completedBoundaryChannel_convolutionAutocorrelation_re_nonnegative_ownerGap
          f (hPrime f))

end

end LFunctions
end Boundary
