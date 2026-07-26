import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ContourAssembly.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.FiniteRectangleResidues.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.OnePoleAffineIntegralZero
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaZeroKreinGram.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaZeroKreinGram.WeilCriterion.OwnerParts.NormalizedSignedBoundary
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaZeroKreinGram.WeilCriterion.OwnerParts.PhysicalContourBoundaryCore
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaCompletedHilbertSource.EndpointTraceDomination
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaZeroTail.TailSummability.Owner

/-!
# Upstream positivity bridge for the final RH wrapper

This file owns the analytic bridge from the completed explicit formula on
autocorrelation probes to the boundary channel.  Contour convergence and
boundary positivity are kept as separate named inputs: a contour identity must
not be presented as a proof of the positivity assertion it transports.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped Topology

/-- A supplied family of horizontal avoiding schedules for all autocorrelation
contour families.  This is the constructive schedule input that avoids using
the canonical selector. -/
structure ZetaCompletedAutocorrelationHorizontalAvoidingScheduleFamily where
  schedule :
    ∀ f : ZetaAdmissibleFunction,
      ZetaAdmissibleFunction.ExplicitFormulaHorizontalAvoidingHeightSchedule
        (ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_contourFamily f)

/-- The right-one correction integral converges to its Cauchy projection along
a supplied avoiding height schedule. -/
theorem zetaCompletedExplicitFormulaCorrectionRightOnePoleVerticalIntegral_tendsto_projection_of_schedule_owner
    (f : ZetaAdmissibleFunction)
    (schedule :
      ZetaAdmissibleFunction.ExplicitFormulaHorizontalAvoidingHeightSchedule
        (ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_contourFamily f))
    (hPhi : ZetaAdmissibleFunction.ZetaPhiAnalyticControl
      (ZetaAdmissibleFunction.convolutionAutocorrelation f))
    (hLog : ZetaAdmissibleFunction.CompletedZetaNegLogDerivControl
      (ZetaAdmissibleFunction.convolutionAutocorrelation f)) :
    Tendsto
      (fun u : ℝ =>
        ZetaAdmissibleFunction.zetaCompletedExplicitFormulaCorrectionRightOnePoleVerticalIntegral
          (ZetaAdmissibleFunction.convolutionAutocorrelation f)
          (ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_contourFamily f)
          ((ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_familyAnalyticPackage
            f
            schedule
            hPhi
            hLog).height_schedule.height u))
      atTop
      (𝓝
          (ZetaAdmissibleFunction.zetaCompletedExplicitFormulaRightOnePoleCauchyProjectionValue
            (ZetaAdmissibleFunction.convolutionAutocorrelation f)
            (ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c)) :=
  ZetaAdmissibleFunction.zetaCompletedExplicitFormulaCorrectionRightOnePoleVerticalIntegral_tendsto_projection_direct_ownerOnePoleAffine
    (ZetaAdmissibleFunction.convolutionAutocorrelation f)
    (ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_contourFamily f)
    (ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_familyAnalyticPackage
      f
      schedule
      hPhi
      hLog)


/-- Scheduled contour convergence along supplied autocorrelation avoiding
height schedules. -/
def ZetaCompletedAutocorrelationScheduledContourLimitOf
    (schedule :
      ∀ f : ZetaAdmissibleFunction,
        ZetaAdmissibleFunction.ExplicitFormulaHorizontalAvoidingHeightSchedule
          (ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_contourFamily f)) :
    Prop :=
  ∀ f : ZetaAdmissibleFunction,
    ∀ hPhi : ZetaAdmissibleFunction.ZetaPhiAnalyticControl
      (ZetaAdmissibleFunction.convolutionAutocorrelation f),
    ∀ hLog : ZetaAdmissibleFunction.CompletedZetaNegLogDerivControl
      (ZetaAdmissibleFunction.convolutionAutocorrelation f),
      Tendsto
        (fun u : ℝ =>
          ZetaAdmissibleFunction.zetaCompletedExplicitFormulaContourIntegral
              (ZetaAdmissibleFunction.convolutionAutocorrelation f)
              ((ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_contourFamily f).rectangle
                ((ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_familyAnalyticPackage
                  f
                  (schedule f)
                  hPhi
                  hLog).height_schedule.height u)))
        atTop
        (𝓝
          (ZetaAdmissibleFunction.zetaCompletedZeroSideComplex
            (ZetaAdmissibleFunction.convolutionAutocorrelation f)))

/-- Scheduled contour convergence along supplied autocorrelation avoiding
height schedules, with fixed-degree scheduled horizontal log-derivative growth. -/
def ZetaCompletedAutocorrelationPolynomialScheduledContourLimitOf
    (schedule :
      ∀ f : ZetaAdmissibleFunction,
        ZetaAdmissibleFunction.ExplicitFormulaHorizontalAvoidingHeightSchedule
          (ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_contourFamily f)) :
    Prop :=
  ∀ f : ZetaAdmissibleFunction,
    ∀ hPhi : ZetaAdmissibleFunction.ZetaPhiAnalyticControl
      (ZetaAdmissibleFunction.convolutionAutocorrelation f),
    ∀ hLog : ZetaAdmissibleFunction.CompletedZetaNegLogDerivControl
      (ZetaAdmissibleFunction.convolutionAutocorrelation f),
    ∀ hPoly :
      ZetaAdmissibleFunction.ExplicitFormulaScheduledPolynomialFamilyAnalyticPackage
        (ZetaAdmissibleFunction.convolutionAutocorrelation f)
        (ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_contourFamily f),
      hPoly.height_schedule =
        (ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_familyAnalyticPackage
          f
          (schedule f)
          hPhi
          hLog).height_schedule →
      Tendsto
        (fun u : ℝ =>
          ZetaAdmissibleFunction.zetaCompletedExplicitFormulaContourIntegral
              (ZetaAdmissibleFunction.convolutionAutocorrelation f)
              ((ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_contourFamily f).rectangle
                ((ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_familyAnalyticPackage
                  f
                  (schedule f)
                  hPhi
                  hLog).height_schedule.height u)))
        atTop
        (𝓝
          (ZetaAdmissibleFunction.zetaCompletedZeroSideComplex
            (ZetaAdmissibleFunction.convolutionAutocorrelation f)))

/-- Scheduled contour convergence along a supplied autocorrelation schedule
family. -/
def ZetaCompletedAutocorrelationScheduledContourLimitOfFamily
    (scheduleFamily :
      ZetaCompletedAutocorrelationHorizontalAvoidingScheduleFamily) :
    Prop :=
  ZetaCompletedAutocorrelationScheduledContourLimitOf scheduleFamily.schedule


/-- Pointwise finite-rectangle residue equality along supplied autocorrelation
avoiding height schedules. -/
def ZetaCompletedAutocorrelationScheduledFiniteResidueEqualityOf
    (schedule :
      ∀ f : ZetaAdmissibleFunction,
        ZetaAdmissibleFunction.ExplicitFormulaHorizontalAvoidingHeightSchedule
          (ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_contourFamily f)) :
    Prop :=
  ∀ f : ZetaAdmissibleFunction,
    ∀ hPhi : ZetaAdmissibleFunction.ZetaPhiAnalyticControl
      (ZetaAdmissibleFunction.convolutionAutocorrelation f),
    ∀ hLog : ZetaAdmissibleFunction.CompletedZetaNegLogDerivControl
      (ZetaAdmissibleFunction.convolutionAutocorrelation f),
      ZetaAdmissibleFunction.zetaCompletedScheduledFiniteResidueEquality
        (ZetaAdmissibleFunction.convolutionAutocorrelation f)
        (ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_contourFamily f)
        (ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_familyAnalyticPackage
          f
          (schedule f)
          hPhi
          hLog)

/-- Pointwise finite-rectangle residue equality along a supplied
autocorrelation schedule family. -/
def ZetaCompletedAutocorrelationScheduledFiniteResidueEqualityOfFamily
    (scheduleFamily :
      ZetaCompletedAutocorrelationHorizontalAvoidingScheduleFamily) :
    Prop :=
  ZetaCompletedAutocorrelationScheduledFiniteResidueEqualityOf scheduleFamily.schedule


/-- The finite-rectangle pointwise residue theorem implies the fixed-degree
scheduled autocorrelation contour limit. -/
theorem zetaCompletedAutocorrelationPolynomialScheduledContourLimitOf_of_finiteResidueEquality
    (schedule :
      ∀ f : ZetaAdmissibleFunction,
        ZetaAdmissibleFunction.ExplicitFormulaHorizontalAvoidingHeightSchedule
          (ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_contourFamily f))
    (hfinite :
      ZetaCompletedAutocorrelationScheduledFiniteResidueEqualityOf schedule) :
    ZetaCompletedAutocorrelationPolynomialScheduledContourLimitOf schedule :=
  fun f hPhi hLog hPoly hschedule =>
    Exists.elim (hfinite f hPhi hLog)
      (fun residueWindowDegree hresidue =>
        Eq.subst
          (motive := fun residueWindowDegreeTransport : ℕ =>
            Tendsto
              (fun u : ℝ =>
                ZetaAdmissibleFunction.zetaCompletedExplicitFormulaContourIntegral
                    (ZetaAdmissibleFunction.convolutionAutocorrelation f)
                    ((ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_contourFamily f).rectangle
                      ((ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_familyAnalyticPackage
                        f
                        (schedule f)
                        hPhi
                        hLog).height_schedule.height u)))
              atTop
              (𝓝
                (ZetaAdmissibleFunction.zetaCompletedZeroSideComplex
                  (ZetaAdmissibleFunction.convolutionAutocorrelation f))))
          (Eq.refl residueWindowDegree)
          (ZetaAdmissibleFunction.zetaCompletedExplicitFormulaContourIntegral_tendsto_zeroSideComplex_of_polynomialScheduledPackage_ownerResidueCalculus
            (ZetaAdmissibleFunction.convolutionAutocorrelation f)
            (ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_verticallyRegularContourFamily f)
            (ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_familyAnalyticPackage
              f
              (schedule f)
              hPhi
              hLog)
            hPoly
            hschedule
            hresidue
            (summable_zetaZeroSideContribution_owner
              (ZetaAdmissibleFunction.convolutionAutocorrelation f))))

/-- A fixed-degree scheduled contour limit supplies the legacy scheduled
contour-limit surface by taking the polynomial scheduled package induced by the
stored full analytic package. -/
theorem zetaCompletedAutocorrelationScheduledContourLimitOf_of_polynomialScheduledContourLimit
    (schedule :
      ∀ f : ZetaAdmissibleFunction,
        ZetaAdmissibleFunction.ExplicitFormulaHorizontalAvoidingHeightSchedule
          (ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_contourFamily f))
    (hpoly :
      ZetaCompletedAutocorrelationPolynomialScheduledContourLimitOf schedule) :
    ZetaCompletedAutocorrelationScheduledContourLimitOf schedule :=
  fun f hPhi hLog =>
    let analyticPackage :
        ZetaAdmissibleFunction.ExplicitFormulaFamilyAnalyticPackage
          (ZetaAdmissibleFunction.convolutionAutocorrelation f)
          (ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_contourFamily f) :=
      ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_familyAnalyticPackage
        f
        (schedule f)
        hPhi
        hLog
    let scheduledPackage :
        ZetaAdmissibleFunction.ExplicitFormulaScheduledFamilyAnalyticPackage
          (ZetaAdmissibleFunction.convolutionAutocorrelation f)
          (ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_contourFamily f) :=
      analyticPackage.toScheduledFamilyAnalyticPackage
    let polynomialPackage :
        ZetaAdmissibleFunction.ExplicitFormulaScheduledPolynomialFamilyAnalyticPackage
          (ZetaAdmissibleFunction.convolutionAutocorrelation f)
          (ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_contourFamily f) :=
      scheduledPackage.toPolynomialGrowthAtDegree 0
    hpoly f hPhi hLog polynomialPackage rfl

/-- A fixed-degree scheduled contour limit supplies the legacy scheduled
contour-limit surface from independent polynomial-growth control. -/
theorem zetaCompletedAutocorrelationScheduledContourLimitOf_of_polynomialGrowthControl
    (schedule :
      ∀ f : ZetaAdmissibleFunction,
        ZetaAdmissibleFunction.ExplicitFormulaHorizontalAvoidingHeightSchedule
          (ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_contourFamily f))
    (hGrowth : ∀ f : ZetaAdmissibleFunction,
      ZetaAdmissibleFunction.CompletedZetaNegLogDerivPolynomialGrowthControl
        (ZetaAdmissibleFunction.convolutionAutocorrelation f))
    (hpoly :
      ZetaCompletedAutocorrelationPolynomialScheduledContourLimitOf schedule) :
    ZetaCompletedAutocorrelationScheduledContourLimitOf schedule :=
  fun f hPhi hLog =>
    let analyticPackage :
        ZetaAdmissibleFunction.ExplicitFormulaFamilyAnalyticPackage
          (ZetaAdmissibleFunction.convolutionAutocorrelation f)
          (ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_contourFamily f) :=
      ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_familyAnalyticPackage
        f
        (schedule f)
        hPhi
        hLog
    Exists.elim
      (analyticPackage.existsPolynomialScheduledPackage_of_polynomialGrowthControl
        (hGrowth f))
      (fun polynomialPackage hschedule =>
        hpoly f hPhi hLog polynomialPackage hschedule)

/-- The finite-rectangle pointwise residue theorem plus independent
polynomial-growth control implies the legacy scheduled autocorrelation contour
limit. -/
theorem zetaCompletedAutocorrelationScheduledContourLimitOf_of_finiteResidueEquality_and_polynomialGrowthControl
    (schedule :
      ∀ f : ZetaAdmissibleFunction,
        ZetaAdmissibleFunction.ExplicitFormulaHorizontalAvoidingHeightSchedule
          (ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_contourFamily f))
    (hfinite :
      ZetaCompletedAutocorrelationScheduledFiniteResidueEqualityOf schedule)
    (hGrowth : ∀ f : ZetaAdmissibleFunction,
      ZetaAdmissibleFunction.CompletedZetaNegLogDerivPolynomialGrowthControl
        (ZetaAdmissibleFunction.convolutionAutocorrelation f)) :
    ZetaCompletedAutocorrelationScheduledContourLimitOf schedule :=
  zetaCompletedAutocorrelationScheduledContourLimitOf_of_polynomialGrowthControl
    schedule
    hGrowth
    (zetaCompletedAutocorrelationPolynomialScheduledContourLimitOf_of_finiteResidueEquality
      schedule
      hfinite)

/-- Completed log-derivative control, Binet coherence, and the scheduled
contour limit give the completed-boundary identification used by
the endpoint-absorption positivity owner. -/
theorem zetaWeilAutocorrelationCompletedBoundaryIdentification_of_contourAssemblyOf
    (schedule :
      ∀ f : ZetaAdmissibleFunction,
        ZetaAdmissibleFunction.ExplicitFormulaHorizontalAvoidingHeightSchedule
          (ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_contourFamily f))
    (hPhi : ∀ f : ZetaAdmissibleFunction,
      ZetaAdmissibleFunction.ZetaPhiAnalyticControl
        (ZetaAdmissibleFunction.convolutionAutocorrelation f))
    (hLog : ∀ f : ZetaAdmissibleFunction,
      ZetaAdmissibleFunction.CompletedZetaNegLogDerivControl
        (ZetaAdmissibleFunction.convolutionAutocorrelation f))
    (hcoh : Complex.gammaBinetPrincipalLogCoherence)
    (hcontour :
      ZetaCompletedAutocorrelationScheduledContourLimitOf schedule) :
    ZetaWeilAutocorrelationCompletedBoundaryIdentification :=
  fun f =>
    ZetaAdmissibleFunction.zetaWeilFormCompleted_convolutionAutocorrelation_eq_completedBoundaryChannel_re_of_constructedScheduledHorizontalCarrier_ownerContourAssembly
      f
      (schedule f)
      (hPhi f)
      (hLog f)
      hcoh
      (zetaCompletedExplicitFormulaCorrectionRightOnePoleVerticalIntegral_tendsto_projection_of_schedule_owner
        f (schedule f) (hPhi f) (hLog f))
      (hcontour f (hPhi f) (hLog f))

/-- Completed-boundary identification from a supplied autocorrelation schedule
family. -/
theorem zetaWeilAutocorrelationCompletedBoundaryIdentification_of_contourAssemblyOfFamily
    (scheduleFamily :
      ZetaCompletedAutocorrelationHorizontalAvoidingScheduleFamily)
    (hPhi : ∀ f : ZetaAdmissibleFunction,
      ZetaAdmissibleFunction.ZetaPhiAnalyticControl
        (ZetaAdmissibleFunction.convolutionAutocorrelation f))
    (hLog : ∀ f : ZetaAdmissibleFunction,
      ZetaAdmissibleFunction.CompletedZetaNegLogDerivControl
        (ZetaAdmissibleFunction.convolutionAutocorrelation f))
    (hcoh : Complex.gammaBinetPrincipalLogCoherence)
    (hcontour :
      ZetaCompletedAutocorrelationScheduledContourLimitOfFamily scheduleFamily) :
    ZetaWeilAutocorrelationCompletedBoundaryIdentification :=
  zetaWeilAutocorrelationCompletedBoundaryIdentification_of_contourAssemblyOf
    scheduleFamily.schedule
    hPhi
    hLog
    hcoh
    hcontour




end

end LFunctions
end Boundary
