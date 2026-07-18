import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ContourAssembly.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.OnePoleAffineIntegralZero
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaZeroKreinGram.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaCompletedHilbertSource.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaZeroKreinGram.WeilCriterion.OwnerParts.CanonicalAnalyticInputs
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaZeroKreinGram.WeilCriterion.OwnerParts.SummedPrimeTransport
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaZeroKreinGram.WeilCriterion.OwnerParts.NormalizedPositiveBoundary

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

/-- Completed two-face ledger cancellation gives the matrix comparison consumed by
the positive boundary realization. -/
theorem completedPrimeTwoFace_matrixComparison_of_ledgerCancellation
    (f : ZetaAdmissibleFunction)
    (hledger :
      ZetaAdmissibleFunction.ZetaCompletedPrimePowerAutocorrelationLedgerCancellation f)
    (horiented :
      Summable
        (fun ι : ZetaPrimePowerIndex =>
          ZetaAdmissibleFunction.zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate
            ι f)) :
    Complex.re
        (ZetaAdmissibleFunction.zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f) =
      Complex.re
        (ZetaAdmissibleFunction.zetaPrimeTwoFaceGNSMatrixCoefficient f) := by
  have hzero :
      Complex.re
          (ZetaAdmissibleFunction.zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f) = 0 :=
    ZetaAdmissibleFunction.completedPrimeTwoFaceGNSMatrixCoefficient_re_eq_zero_boundaryCancellation
      f hledger horiented
  exact
    (ZetaAdmissibleFunction.matrixComparison_iff_completedPrimeTwoFaceGNSMatrixCoefficient_re_eq_zero
      f).mpr hzero

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
    (hone :
      Tendsto
        (fun u : ℝ =>
          ZetaAdmissibleFunction.zetaCompletedExplicitFormulaCorrectionRightOnePoleVerticalIntegral
            (ZetaAdmissibleFunction.convolutionAutocorrelation f)
            (ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_contourFamily f)
            ((ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_familyAnalyticPackage
              f schedule hPhi hLog).height_schedule.height u))
        atTop
        (𝓝 (ZetaAdmissibleFunction.zetaCompletedExplicitFormulaRightOnePoleCauchyProjectionValue
          (ZetaAdmissibleFunction.convolutionAutocorrelation f)
          (ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c)))
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
      f schedule hPhi hLog hone hcontourScheduled E hTopMem hBottomMem

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
    (hone :
      ∀ f : ZetaAdmissibleFunction,
        Tendsto
          (fun u : ℝ =>
            ZetaAdmissibleFunction.zetaCompletedExplicitFormulaCorrectionRightOnePoleVerticalIntegral
              (ZetaAdmissibleFunction.convolutionAutocorrelation f)
              (ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_contourFamily f)
              ((ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_familyAnalyticPackage
                f (hschedule f) (hPhi f) (hLog f)).height_schedule.height u))
          atTop
          (𝓝 (ZetaAdmissibleFunction.zetaCompletedExplicitFormulaRightOnePoleCauchyProjectionValue
            (ZetaAdmissibleFunction.convolutionAutocorrelation f)
            (ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c)))
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
    (hTransport :
      ∀ f : ZetaAdmissibleFunction,
        ZetaAdmissibleFunction.CompletedSummedPrimeContourTimeTransport f)
    (hledger :
      ∀ f : ZetaAdmissibleFunction,
        ZetaAdmissibleFunction.ZetaCompletedPrimePowerAutocorrelationLedgerCancellation f)
    (horiented :
      ∀ f : ZetaAdmissibleFunction,
        Summable
          (fun ι : ZetaPrimePowerIndex =>
            ZetaAdmissibleFunction.zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate
              ι f)) :
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
          f (hschedule f) (hPhi f) (hLog f) (hone f) (hcontourScheduled f) (E f) (hTopMem f) (hBottomMem f)
      have hmatrix :
          Complex.re
              (ZetaAdmissibleFunction.zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f) =
            Complex.re
              (ZetaAdmissibleFunction.zetaPrimeTwoFaceGNSMatrixCoefficient f) :=
        completedPrimeTwoFace_matrixComparison_of_ledgerCancellation
          f (hledger f) (horiented f)
      Eq.subst
        (motive := fun x : ℝ => 0 ≤ x)
        hbridge.symm
        (ZetaAdmissibleFunction.completedBoundaryChannel_convolutionAutocorrelation_re_nonnegative_of_summedTransport
          f (hTransport f) hmatrix)

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
    (hone :
      Tendsto
        (fun u : ℝ =>
          ZetaAdmissibleFunction.zetaCompletedExplicitFormulaCorrectionRightOnePoleVerticalIntegral
            (ZetaAdmissibleFunction.convolutionAutocorrelation f)
            (ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_contourFamily f)
            ((ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_familyAnalyticPackage
              f schedule hPhi hLog).height_schedule.height u))
        atTop
        (𝓝 (ZetaAdmissibleFunction.zetaCompletedExplicitFormulaRightOnePoleCauchyProjectionValue
          (ZetaAdmissibleFunction.convolutionAutocorrelation f)
          (ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c)))
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
      f schedule hPhi hLog hone hcontourScheduled

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
    (hone :
      Tendsto
        (fun u : ℝ =>
          ZetaAdmissibleFunction.zetaCompletedExplicitFormulaCorrectionRightOnePoleVerticalIntegral
            (ZetaAdmissibleFunction.convolutionAutocorrelation f)
            (ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_contourFamily f)
            ((ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_familyAnalyticPackage
              f schedule hPhi hLog).height_schedule.height u))
        atTop
        (𝓝 (ZetaAdmissibleFunction.zetaCompletedExplicitFormulaRightOnePoleCauchyProjectionValue
          (ZetaAdmissibleFunction.convolutionAutocorrelation f)
          (ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c)))
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
      f schedule hPhi hLog hone N hfinite hsum

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
    (hone :
      ∀ f : ZetaAdmissibleFunction,
        Tendsto
          (fun u : ℝ =>
            ZetaAdmissibleFunction.zetaCompletedExplicitFormulaCorrectionRightOnePoleVerticalIntegral
              (ZetaAdmissibleFunction.convolutionAutocorrelation f)
              (ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_contourFamily f)
              ((ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_familyAnalyticPackage
                f (hschedule f) (hPhi f) (hLog f)).height_schedule.height u))
          atTop
          (𝓝 (ZetaAdmissibleFunction.zetaCompletedExplicitFormulaRightOnePoleCauchyProjectionValue
            (ZetaAdmissibleFunction.convolutionAutocorrelation f)
            (ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c)))
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
    (hTransport :
      ∀ f : ZetaAdmissibleFunction,
        ZetaAdmissibleFunction.CompletedSummedPrimeContourTimeTransport f)
    (hledger :
      ∀ f : ZetaAdmissibleFunction,
        ZetaAdmissibleFunction.ZetaCompletedPrimePowerAutocorrelationLedgerCancellation f)
    (horiented :
      ∀ f : ZetaAdmissibleFunction,
        Summable
          (fun ι : ZetaPrimePowerIndex =>
            ZetaAdmissibleFunction.zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate
              ι f)) :
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
          f (hschedule f) (hPhi f) (hLog f) (hone f) (hcontourScheduled f)
      have hmatrix :
          Complex.re
              (ZetaAdmissibleFunction.zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f) =
            Complex.re
              (ZetaAdmissibleFunction.zetaPrimeTwoFaceGNSMatrixCoefficient f) :=
        completedPrimeTwoFace_matrixComparison_of_ledgerCancellation
          f (hledger f) (horiented f)
      Eq.subst
        (motive := fun x : ℝ => 0 ≤ x)
        hbridge.symm
        (ZetaAdmissibleFunction.completedBoundaryChannel_convolutionAutocorrelation_re_nonnegative_of_summedTransport
          f (hTransport f) hmatrix)

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
    (hone :
      ∀ f : ZetaAdmissibleFunction,
        Tendsto
          (fun u : ℝ =>
            ZetaAdmissibleFunction.zetaCompletedExplicitFormulaCorrectionRightOnePoleVerticalIntegral
              (ZetaAdmissibleFunction.convolutionAutocorrelation f)
              (ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_contourFamily f)
              ((ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_familyAnalyticPackage
                f (hschedule f) (hPhi f) (hLog f)).height_schedule.height u))
          atTop
          (𝓝 (ZetaAdmissibleFunction.zetaCompletedExplicitFormulaRightOnePoleCauchyProjectionValue
            (ZetaAdmissibleFunction.convolutionAutocorrelation f)
            (ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c)))
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
    (hTransport :
      ∀ f : ZetaAdmissibleFunction,
        ZetaAdmissibleFunction.CompletedSummedPrimeContourTimeTransport f)
    (hledger :
      ∀ f : ZetaAdmissibleFunction,
        ZetaAdmissibleFunction.ZetaCompletedPrimePowerAutocorrelationLedgerCancellation f)
    (horiented :
      ∀ f : ZetaAdmissibleFunction,
        Summable
          (fun ι : ZetaPrimePowerIndex =>
            ZetaAdmissibleFunction.zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate
              ι f)) :
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
          f (hschedule f) (hPhi f) (hLog f) (hone f) N (hfinite f) (hsum f)
      have hmatrix :
          Complex.re
              (ZetaAdmissibleFunction.zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f) =
            Complex.re
              (ZetaAdmissibleFunction.zetaPrimeTwoFaceGNSMatrixCoefficient f) :=
        completedPrimeTwoFace_matrixComparison_of_ledgerCancellation
          f (hledger f) (horiented f)
      Eq.subst
        (motive := fun x : ℝ => 0 ≤ x)
        hbridge.symm
        (ZetaAdmissibleFunction.completedBoundaryChannel_convolutionAutocorrelation_re_nonnegative_of_summedTransport
          f (hTransport f) hmatrix)

/-- The right-one correction integral converges to its Cauchy projection along
the canonical avoiding height schedule. -/
theorem zetaCompletedExplicitFormulaCorrectionRightOnePoleVerticalIntegral_tendsto_projection_owner
    (f : ZetaAdmissibleFunction) :
    Tendsto
      (fun u : ℝ =>
        ZetaAdmissibleFunction.zetaCompletedExplicitFormulaCorrectionRightOnePoleVerticalIntegral
          (ZetaAdmissibleFunction.convolutionAutocorrelation f)
          (ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_contourFamily f)
          ((ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_familyAnalyticPackage
            f
            (ZetaAdmissibleFunction.zetaCompletedExplicitFormulaAutocorrelationHorizontalAvoidingSchedule f)
            (zetaPhiAnalyticControl_of_admissible
              (ZetaAdmissibleFunction.convolutionAutocorrelation f))
            (completedZetaNegLogDerivControl
              (ZetaAdmissibleFunction.convolutionAutocorrelation f))).height_schedule.height u))
      atTop
      (𝓝
        (ZetaAdmissibleFunction.zetaCompletedExplicitFormulaRightOnePoleCauchyProjectionValue
          (ZetaAdmissibleFunction.convolutionAutocorrelation f)
          (ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c)) := by
  exact
    ZetaAdmissibleFunction.zetaCompletedExplicitFormulaCorrectionRightOnePoleVerticalIntegral_tendsto_projection_direct_ownerOnePoleAffine
      (ZetaAdmissibleFunction.convolutionAutocorrelation f)
      (ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_contourFamily f)
      (ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_familyAnalyticPackage
        f
        (ZetaAdmissibleFunction.zetaCompletedExplicitFormulaAutocorrelationHorizontalAvoidingSchedule f)
        (zetaPhiAnalyticControl_of_admissible
          (ZetaAdmissibleFunction.convolutionAutocorrelation f))
        (completedZetaNegLogDerivControl
          (ZetaAdmissibleFunction.convolutionAutocorrelation f)))

/-- The scheduled normalized pole-corrected contour integrals converge to the
completed-zero side of the autocorrelation probe. -/
theorem zetaCompletedExplicitFormulaAutocorrelationNormalizedPoleCorrectedContour_tendsto_zeroSide_owner
    (f : ZetaAdmissibleFunction)
    (zeroSideSummable :
      Summable
        (fun rho : {rho : ℂ // ZetaCompletedZero rho} =>
          zetaZeroSideContribution (rho : ℂ)
            (ZetaAdmissibleFunction.convolutionAutocorrelation f))) :
    Tendsto
      (fun u : ℝ =>
        ZetaAdmissibleFunction.explicitFormulaRectangleNormalizedPoleCorrectedContourIntegral
          (ZetaAdmissibleFunction.convolutionAutocorrelation f)
          (ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_contourFamily f)
          ((ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_familyAnalyticPackage
            f
            (ZetaAdmissibleFunction.zetaCompletedExplicitFormulaAutocorrelationHorizontalAvoidingSchedule f)
            (zetaPhiAnalyticControl_of_admissible
              (ZetaAdmissibleFunction.convolutionAutocorrelation f))
            (completedZetaNegLogDerivControl
              (ZetaAdmissibleFunction.convolutionAutocorrelation f))).height_schedule.height u))
      atTop
      (𝓝 (ZetaAdmissibleFunction.zetaCompletedZeroSideComplex
        (ZetaAdmissibleFunction.convolutionAutocorrelation f))) := by
  let probe : ZetaAdmissibleFunction :=
    ZetaAdmissibleFunction.convolutionAutocorrelation f
  let family : ZetaAdmissibleFunction.ExplicitFormulaContourFamily :=
    ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_contourFamily f
  let analyticPackage :
      ZetaAdmissibleFunction.ExplicitFormulaFamilyAnalyticPackage probe family :=
    ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_familyAnalyticPackage
      f
      (ZetaAdmissibleFunction.zetaCompletedExplicitFormulaAutocorrelationHorizontalAvoidingSchedule f)
      (zetaPhiAnalyticControl_of_admissible probe)
      (completedZetaNegLogDerivControl probe)
  exact
    match analyticPackage.scheduled_horizontalFamilyZeroExcisedStrip with
    | ⟨carrier, topMem, bottomMem⟩ =>
        ZetaAdmissibleFunction.explicitFormulaRectangleNormalizedPoleCorrectedContourIntegral_tendsto_zeroSideComplex
          probe family analyticPackage carrier topMem bottomMem zeroSideSummable

/-- The normalized standard contour boundary is the completed zero side of an
autocorrelation probe. -/
theorem zetaCompletedExplicitFormulaNormalizedStandardContourBoundarySum_eq_zeroSide_owner
    (f : ZetaAdmissibleFunction)
    (gammaCoherence : Complex.gammaBinetPrincipalLogCoherence)
    (zeroSideSummable :
      Summable
        (fun rho : {rho : ℂ // ZetaCompletedZero rho} =>
          zetaZeroSideContribution (rho : ℂ)
            (ZetaAdmissibleFunction.convolutionAutocorrelation f))) :
    ZetaAdmissibleFunction.zetaCompletedExplicitFormulaNormalizedStandardContourBoundarySum
        (ZetaAdmissibleFunction.convolutionAutocorrelation f) =
      ZetaAdmissibleFunction.zetaCompletedZeroSideComplex
        (ZetaAdmissibleFunction.convolutionAutocorrelation f) := by
  let probe : ZetaAdmissibleFunction :=
    ZetaAdmissibleFunction.convolutionAutocorrelation f
  let family : ZetaAdmissibleFunction.ExplicitFormulaContourFamily :=
    ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_contourFamily f
  let analyticPackage :
      ZetaAdmissibleFunction.ExplicitFormulaFamilyAnalyticPackage probe family :=
    ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_familyAnalyticPackage
      f
      (ZetaAdmissibleFunction.zetaCompletedExplicitFormulaAutocorrelationHorizontalAvoidingSchedule f)
      (zetaPhiAnalyticControl_of_admissible probe)
      (completedZetaNegLogDerivControl probe)
  have verticalLimit :
      Tendsto
        (fun u : ℝ =>
          ZetaAdmissibleFunction.zetaCompletedExplicitFormulaRightLineIntegral probe
              (family.rectangle (analyticPackage.height_schedule.height u)) -
            ZetaAdmissibleFunction.zetaCompletedExplicitFormulaLeftLineIntegral probe
              (family.rectangle (analyticPackage.height_schedule.height u)))
        atTop
        (𝓝
          (ZetaAdmissibleFunction.zetaCompletedExplicitFormulaStandardContourBoundarySum
            probe)) := by
    exact
      ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_scheduledVertical_tendsto_boundarySum
        f
        (ZetaAdmissibleFunction.zetaCompletedExplicitFormulaAutocorrelationHorizontalAvoidingSchedule f)
        (zetaPhiAnalyticControl_of_admissible probe)
        (completedZetaNegLogDerivControl probe)
        gammaCoherence
        (zetaCompletedExplicitFormulaCorrectionRightOnePoleVerticalIntegral_tendsto_projection_owner f)
  exact
    match analyticPackage.scheduled_horizontalFamilyZeroExcisedStrip with
    | ⟨carrier, topMem, bottomMem⟩ =>
        ZetaAdmissibleFunction.zetaCompletedExplicitFormulaNormalizedStandardContourBoundarySum_eq_zeroSideComplex
          probe family analyticPackage carrier topMem bottomMem zeroSideSummable verticalLimit

/-- The remaining normalization comparison identifies the contour-derived
boundary with the public time-side boundary on autocorrelation probes. -/
theorem zetaCompletedExplicitFormulaNormalizedStandardContourBoundarySum_eq_completedBoundaryChannel_autocorrelation_owner
    (f : ZetaAdmissibleFunction) :
    ZetaAdmissibleFunction.zetaCompletedExplicitFormulaNormalizedStandardContourBoundarySum
        (ZetaAdmissibleFunction.convolutionAutocorrelation f) =
      ZetaAdmissibleFunction.completedBoundaryChannel
        (ZetaAdmissibleFunction.convolutionAutocorrelation f) := by
  let probe : ZetaAdmissibleFunction :=
    ZetaAdmissibleFunction.convolutionAutocorrelation f
  have hnormalized :
      ZetaAdmissibleFunction.zetaCompletedExplicitFormulaNormalizedStandardContourBoundarySum
          probe =
        ZetaAdmissibleFunction.zetaCompletedExplicitFormulaPrimeNaturalTwoFaceBoundaryContribution
              probe /
            ZetaAdmissibleFunction.explicitFormulaTwoPi +
          ZetaAdmissibleFunction.zetaCompletedExplicitFormulaArchimedeanContribution
              probe /
            ZetaAdmissibleFunction.explicitFormulaTwoPi :=
    ZetaAdmissibleFunction.zetaCompletedExplicitFormulaNormalizedStandardContourBoundarySum_eq_prime_add_archimedean_div
      probe
  have hprime :
      ZetaAdmissibleFunction.zetaCompletedExplicitFormulaPrimeNaturalTwoFaceBoundaryContribution
            probe /
          ZetaAdmissibleFunction.explicitFormulaTwoPi =
        -(ZetaAdmissibleFunction.zetaCompletedExplicitFormulaPrimeContribution probe) :=
    ZetaAdmissibleFunction.zetaCompletedExplicitFormulaPrimeNaturalTwoFaceBoundaryContribution_div_twoPi_eq_neg_primeContribution_autocorrelation
      f
  have htwoPi :
      ZetaAdmissibleFunction.explicitFormulaTwoPi =
        2 * (Real.pi : ℂ) :=
    Eq.refl _
  exact Eq.trans hnormalized
    (Eq.trans
      (congrArg₂ HAdd.hAdd hprime
        (congrArg
          (fun denominator : ℂ =>
            ZetaAdmissibleFunction.zetaCompletedExplicitFormulaArchimedeanContribution
              probe / denominator)
          htwoPi))
      (ZetaAdmissibleFunction.completedBoundaryChannel_eq_normalized_prime_archimedean
        probe).symm)

/-- The completed contour formula identifies the Weil form with the real
completed boundary channel on every autocorrelation probe. -/
theorem zetaWeilFormCompleted_convolutionAutocorrelation_eq_completedBoundaryChannel_re_owner
    (f : ZetaAdmissibleFunction)
    (gammaCoherence : Complex.gammaBinetPrincipalLogCoherence)
    (zeroSideSummable :
      Summable
        (fun rho : {rho : ℂ // ZetaCompletedZero rho} =>
          zetaZeroSideContribution (rho : ℂ)
            (ZetaAdmissibleFunction.convolutionAutocorrelation f))) :
    zetaWeilFormCompleted
        (ZetaAdmissibleFunction.convolutionAutocorrelation f) =
      Complex.re
        (ZetaAdmissibleFunction.completedBoundaryChannel
          (ZetaAdmissibleFunction.convolutionAutocorrelation f)) := by
  have contourToZero :=
    zetaCompletedExplicitFormulaNormalizedStandardContourBoundarySum_eq_zeroSide_owner
      f gammaCoherence zeroSideSummable
  have contourToBoundary :=
    zetaCompletedExplicitFormulaNormalizedStandardContourBoundarySum_eq_completedBoundaryChannel_autocorrelation_owner
      f
  have zeroToBoundary :
      ZetaAdmissibleFunction.zetaCompletedZeroSideComplex
          (ZetaAdmissibleFunction.convolutionAutocorrelation f) =
        ZetaAdmissibleFunction.completedBoundaryChannel
          (ZetaAdmissibleFunction.convolutionAutocorrelation f) :=
    Eq.trans contourToZero.symm contourToBoundary
  exact Eq.trans
    (zetaWeilFormCompleted_convolutionAutocorrelation_eq_zeroSide f)
    (congrArg Complex.re zeroToBoundary)

/-- The completed boundary channel is nonnegative on every autocorrelation
probe after the physical prime channel is reconstructed in the completed GNS
presentation. -/
theorem completedBoundaryChannel_convolutionAutocorrelation_re_nonnegative_owner
    (f : ZetaAdmissibleFunction)
    (summedTransport :
      ZetaAdmissibleFunction.CompletedSummedPrimeContourTimeTransport f)
    (matrixComparison :
      Complex.re
          (ZetaAdmissibleFunction.zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f) =
        Complex.re
          (ZetaAdmissibleFunction.zetaPrimeTwoFaceGNSMatrixCoefficient f)) :
    0 ≤ Complex.re
      (ZetaAdmissibleFunction.completedBoundaryChannel
        (ZetaAdmissibleFunction.convolutionAutocorrelation f)) := by
  have primePositive :
      Complex.re
          (ZetaAdmissibleFunction.primeBoundaryChannel
            (ZetaAdmissibleFunction.convolutionAutocorrelation f)) =
        ZetaAdmissibleFunction.completedPrimeDefectKernelPositiveChannel f :=
    ZetaAdmissibleFunction.primeBoundaryChannel_convolutionAutocorrelation_re_eq_positiveChannel_of_summedTransport
      f
      summedTransport
      matrixComparison
  exact
    ZetaAdmissibleFunction.completedBoundaryChannel_convolutionAutocorrelation_re_nonnegative_of_normalizedPrime
      f primePositive

/-- Completed Weil positivity assembled at the analytic contour/GNS owner. -/
theorem zetaWeilQuadraticPositivity_owner
    (gammaCoherence : Complex.gammaBinetPrincipalLogCoherence)
    (zeroSideSummable :
      ∀ f : ZetaAdmissibleFunction,
        Summable
          (fun rho : {rho : ℂ // ZetaCompletedZero rho} =>
            zetaZeroSideContribution (rho : ℂ)
              (ZetaAdmissibleFunction.convolutionAutocorrelation f)))
    (summedTransport :
      ∀ f : ZetaAdmissibleFunction,
        ZetaAdmissibleFunction.CompletedSummedPrimeContourTimeTransport f)
    (matrixComparison :
      ∀ f : ZetaAdmissibleFunction,
        Complex.re
            (ZetaAdmissibleFunction.zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f) =
          Complex.re
            (ZetaAdmissibleFunction.zetaPrimeTwoFaceGNSMatrixCoefficient f)) :
    ZetaWeilQuadraticPositivity := by
  exact fun f =>
    Eq.subst
      (motive := fun value : ℝ => 0 ≤ value)
      (zetaWeilFormCompleted_convolutionAutocorrelation_eq_completedBoundaryChannel_re_owner
        f gammaCoherence (zeroSideSummable f)).symm
      (completedBoundaryChannel_convolutionAutocorrelation_re_nonnegative_owner
        f (summedTransport f) (matrixComparison f))

end

end LFunctions
end Boundary
