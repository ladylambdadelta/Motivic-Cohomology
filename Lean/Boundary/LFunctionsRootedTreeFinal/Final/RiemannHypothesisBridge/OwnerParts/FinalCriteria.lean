import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.OwnerParts.TraceBesselCriteria
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaZeroKreinGram.WeilCriterion.OwnerParts.CanonicalScheduleCompatibility
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.GammaBinetStirling.CoherenceComponents

namespace Boundary
namespace LFunctions

noncomputable section

open Filter
open scoped Topology

theorem finalRiemannHypothesis_zetaWeilQuadraticPositivity :
    FinalEndpointTraceReserveDomination →
    ZetaWeilAutocorrelationBoundaryIdentification →
    ZetaWeilQuadraticPositivity :=
  fun reserveDomination hBoundary =>
    (fun reserveInput : FinalEndpointTraceReserveDomination =>
      zetaWeilQuadraticPositivity_of_boundaryIdentification_owner hBoundary)
      reserveDomination

theorem finalRiemannHypothesis_zetaWeilQuadraticPositivity_completedBoundary :
    FinalEndpointTraceReserveDomination →
    ZetaWeilAutocorrelationCompletedBoundaryIdentification →
    ZetaWeilQuadraticPositivity :=
  fun reserveDomination hBoundary =>
    zetaWeilQuadraticPositivity_completedBoundary_owner
      hBoundary
      (finalPhysicalArchimedeanAbsorption_of_endpointTraceReserveDomination
        reserveDomination)

theorem finalRiemannHypothesis_zetaWeilQuadraticPositivity_of_logDerivControl
    (reserveDomination : FinalEndpointTraceReserveDomination)
    (hPhi : ∀ f : ZetaAdmissibleFunction,
      ZetaAdmissibleFunction.ZetaPhiAnalyticControl
        (ZetaAdmissibleFunction.convolutionAutocorrelation f))
    (hLog : ∀ f : ZetaAdmissibleFunction,
      ZetaAdmissibleFunction.CompletedZetaNegLogDerivControl
        (ZetaAdmissibleFunction.convolutionAutocorrelation f)) :
    ZetaWeilQuadraticPositivity :=
  finalRiemannHypothesis_zetaWeilQuadraticPositivity
    reserveDomination
    (finalRiemannHypothesis_boundaryIdentification_of_logDerivControl hPhi hLog)

/-- Concrete completed-log-derivative control supplies the normalized boundary
identification directly.  This is the unconditional candidate route and does not
carry the legacy finite-residue or Gamma-slit inputs. -/
theorem finalRiemannHypothesis_zetaWeilQuadraticPositivity_of_concreteLogDeriv_normalizedBoundary
    (hConcrete :
      ZetaAdmissibleFunction.CompletedZetaNegLogDerivAutocorrelationConcreteControl) :
    ZetaWeilQuadraticPositivity :=
  zetaWeilQuadraticPositivity_of_completedBoundaryConcreteLogDerivativeOwner hConcrete

/-- Concrete completed-log-derivative control and canonical finite-residue
equality give the raw Weil positivity input through the completed-boundary
contour lane. -/
theorem finalRiemannHypothesis_zetaWeilQuadraticPositivity_of_concreteLogDeriv_canonicalGammaBinetFiniteResidueContourAssembly
    (hConcrete :
      ZetaAdmissibleFunction.CompletedZetaNegLogDerivAutocorrelationConcreteControl)
    (hGamma_slit : Complex.GammaRightHalfPlaneSlitPlaneControl)
    (hfinite : ZetaCompletedAutocorrelationScheduledFiniteResidueEquality) :
    ZetaWeilQuadraticPositivity :=
  zetaWeilQuadraticPositivity_of_completedBoundaryScheduledResidueOwnerInputs
    hConcrete
    hGamma_slit
    hfinite

/-- Concrete completed-log-derivative control and canonical pointwise
finite-rectangle residue equality give the raw Weil positivity input through
the completed-boundary contour lane. -/
theorem finalRiemannHypothesis_zetaWeilQuadraticPositivity_of_concreteLogDeriv_canonicalGammaBinetPointwiseFiniteRectangleResidue
    (hConcrete :
      ZetaAdmissibleFunction.CompletedZetaNegLogDerivAutocorrelationConcreteControl)
    (hGamma_slit : Complex.GammaRightHalfPlaneSlitPlaneControl)
    (hfinite :
      ∀ f : ZetaAdmissibleFunction,
        ∀ hPhi : ZetaAdmissibleFunction.ZetaPhiAnalyticControl
          (ZetaAdmissibleFunction.convolutionAutocorrelation f),
        ∀ hLog : ZetaAdmissibleFunction.CompletedZetaNegLogDerivControl
          (ZetaAdmissibleFunction.convolutionAutocorrelation f),
        ∀ u : ℝ,
          ZetaAdmissibleFunction.zetaCompletedExplicitFormulaContourIntegral
              (ZetaAdmissibleFunction.convolutionAutocorrelation f)
              ((ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_contourFamily f).rectangle
                ((ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_familyAnalyticPackage
                  f
                  (ZetaAdmissibleFunction.zetaCompletedExplicitFormulaAutocorrelationHorizontalAvoidingSchedule f)
                  hPhi
                  hLog).height_schedule.height u)) =
            ZetaAdmissibleFunction.explicitFormulaCompletedZeroContourHeightWindowResidueSum
              (ZetaAdmissibleFunction.convolutionAutocorrelation f)
              ((ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_familyAnalyticPackage
                f
                (ZetaAdmissibleFunction.zetaCompletedExplicitFormulaAutocorrelationHorizontalAvoidingSchedule f)
                hPhi
                hLog).height_schedule.height u)) :
    ZetaWeilQuadraticPositivity :=
  zetaWeilQuadraticPositivity_of_completedBoundaryPointwiseFiniteRectangleResidueOwnerInputs
    hConcrete
    hGamma_slit
    hfinite

/-- Concrete completed-log-derivative control and canonical height-window
residue equality give the raw Weil positivity input through the
completed-boundary contour lane. -/
theorem finalRiemannHypothesis_zetaWeilQuadraticPositivity_of_concreteLogDeriv_canonicalGammaBinetHeightWindowResidueContourAssembly
    (hConcrete :
      ZetaAdmissibleFunction.CompletedZetaNegLogDerivAutocorrelationConcreteControl)
    (hGamma_slit : Complex.GammaRightHalfPlaneSlitPlaneControl)
    (hheight : ZetaCompletedAutocorrelationCanonicalHeightWindowResidueEquality) :
    ZetaWeilQuadraticPositivity :=
  zetaWeilQuadraticPositivity_of_completedBoundaryDirectOwnerInputs
    hConcrete
    hGamma_slit
    hheight

theorem finalRiemannHypothesis_centeredZeroCriterion_of_concreteLogDeriv_canonicalGammaBinetHeightWindowResidueContourAssembly
    (hConcrete :
      ZetaAdmissibleFunction.CompletedZetaNegLogDerivAutocorrelationConcreteControl)
    (hGamma_slit : Complex.GammaRightHalfPlaneSlitPlaneControl)
    (hheight : ZetaCompletedAutocorrelationCanonicalHeightWindowResidueEquality) :
    ∀ s : ℂ,
      riemannZeta (1 / 2 + s) = 0 →
        (¬ ∃ n : ℕ, 1 / 2 + s = -2 * (n + 1)) →
          (1 / 2 + s) ≠ 1 →
            s.re = 0 :=
  finalRiemannHypothesis_centeredZeroCriterion_of_zetaWeilQuadraticPositivity
    (finalRiemannHypothesis_zetaWeilQuadraticPositivity_of_concreteLogDeriv_canonicalGammaBinetHeightWindowResidueContourAssembly
      hConcrete
      hGamma_slit
      hheight)

theorem finalRiemannHypothesis_completedBoundaryIdentification_of_contourAssemblyOf
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
  zetaWeilAutocorrelationCompletedBoundaryIdentification_of_contourAssemblyOf
    schedule hPhi hLog hcoh hcontour

theorem finalRiemannHypothesis_completedBoundaryIdentification_of_finiteResidueContourAssemblyOf
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
    (hGrowth : ∀ f : ZetaAdmissibleFunction,
      ZetaAdmissibleFunction.CompletedZetaNegLogDerivPolynomialGrowthControl
        (ZetaAdmissibleFunction.convolutionAutocorrelation f))
    (hcoh : Complex.gammaBinetPrincipalLogCoherence)
    (hfinite :
      ZetaCompletedAutocorrelationScheduledFiniteResidueEqualityOf schedule) :
    ZetaWeilAutocorrelationCompletedBoundaryIdentification :=
  finalRiemannHypothesis_completedBoundaryIdentification_of_contourAssemblyOf
    schedule
    hPhi
    hLog
    hcoh
    (zetaCompletedAutocorrelationScheduledContourLimitOf_of_finiteResidueEquality_and_polynomialGrowthControl
      schedule
      hfinite
      hGrowth)

theorem finalRiemannHypothesis_completedBoundaryIdentification_of_gammaBinetFiniteResidueContourAssemblyOf
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
    (hGamma_slit : Complex.GammaRightHalfPlaneSlitPlaneControl)
    (hfiniteBinet : Complex.BinetAbelPlanaRightHalfPlaneFiniteDecomposition)
    (hfinite :
      ZetaCompletedAutocorrelationScheduledFiniteResidueEqualityOf schedule) :
    ZetaWeilAutocorrelationCompletedBoundaryIdentification :=
  finalRiemannHypothesis_completedBoundaryIdentification_of_finiteResidueContourAssemblyOf
    schedule
    hPhi
    hLog
    (ZetaAdmissibleFunction.completedZetaNegLogDerivPolynomialGrowthControl_autocorrelation_of_fullControl
      hLog)
    (Complex.gammaBinetPrincipalLogCoherence_of_ownerInputs
      hGamma_slit
      hfiniteBinet)
    hfinite

theorem finalRiemannHypothesis_completedBoundaryIdentification_of_canonicalGammaBinetFiniteResidueContourAssemblyOf
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
    (hGamma_slit : Complex.GammaRightHalfPlaneSlitPlaneControl)
    (hfinite :
      ZetaCompletedAutocorrelationScheduledFiniteResidueEqualityOf schedule) :
    ZetaWeilAutocorrelationCompletedBoundaryIdentification :=
  finalRiemannHypothesis_completedBoundaryIdentification_of_gammaBinetFiniteResidueContourAssemblyOf
    schedule
    hPhi
    hLog
    hGamma_slit
    Complex.binetAbelPlanaRightHalfPlaneFiniteDecomposition_owner
    hfinite

theorem finalRiemannHypothesis_completedBoundaryIdentification_of_canonicalFiniteResidueContourAssembly
    (hPhi : ∀ f : ZetaAdmissibleFunction,
      ZetaAdmissibleFunction.ZetaPhiAnalyticControl
        (ZetaAdmissibleFunction.convolutionAutocorrelation f))
    (hLog : ∀ f : ZetaAdmissibleFunction,
      ZetaAdmissibleFunction.CompletedZetaNegLogDerivControl
        (ZetaAdmissibleFunction.convolutionAutocorrelation f))
    (hcoh : Complex.gammaBinetPrincipalLogCoherence)
    (hfinite : ZetaCompletedAutocorrelationScheduledFiniteResidueEquality) :
    ZetaWeilAutocorrelationCompletedBoundaryIdentification :=
  finalRiemannHypothesis_completedBoundaryIdentification_of_finiteResidueContourAssemblyOf
    (fun f =>
      ZetaAdmissibleFunction.zetaCompletedExplicitFormulaAutocorrelationHorizontalAvoidingSchedule
        f)
    hPhi
    hLog
    (ZetaAdmissibleFunction.completedZetaNegLogDerivPolynomialGrowthControl_autocorrelation_of_fullControl
      hLog)
    hcoh
    hfinite

theorem finalRiemannHypothesis_completedBoundaryIdentification_of_canonicalGammaBinetFiniteResidueContourAssembly
    (hPhi : ∀ f : ZetaAdmissibleFunction,
      ZetaAdmissibleFunction.ZetaPhiAnalyticControl
        (ZetaAdmissibleFunction.convolutionAutocorrelation f))
    (hLog : ∀ f : ZetaAdmissibleFunction,
      ZetaAdmissibleFunction.CompletedZetaNegLogDerivControl
        (ZetaAdmissibleFunction.convolutionAutocorrelation f))
    (hGamma_slit : Complex.GammaRightHalfPlaneSlitPlaneControl)
    (hfinite : ZetaCompletedAutocorrelationScheduledFiniteResidueEquality) :
    ZetaWeilAutocorrelationCompletedBoundaryIdentification :=
  finalRiemannHypothesis_completedBoundaryIdentification_of_canonicalGammaBinetFiniteResidueContourAssemblyOf
    (fun f =>
      ZetaAdmissibleFunction.zetaCompletedExplicitFormulaAutocorrelationHorizontalAvoidingSchedule
        f)
    hPhi
    hLog
    hGamma_slit
    hfinite

theorem finalRiemannHypothesis_centeredZeroCriterion :
    FinalEndpointTraceReserveDomination →
    ZetaWeilAutocorrelationBoundaryIdentification →
    ∀ s : ℂ,
      riemannZeta (1 / 2 + s) = 0 →
        (¬ ∃ n : ℕ, 1 / 2 + s = -2 * (n + 1)) →
          (1 / 2 + s) ≠ 1 →
            s.re = 0 :=
  fun reserveDomination hBoundary =>
    finalRiemannHypothesis_centeredZeroCriterion_of_zetaWeilQuadraticPositivity
      (finalRiemannHypothesis_zetaWeilQuadraticPositivity reserveDomination hBoundary)

theorem finalRiemannHypothesis_centeredZeroCriterion_completedBoundary :
    FinalEndpointTraceReserveDomination →
    ZetaWeilAutocorrelationCompletedBoundaryIdentification →
    ∀ s : ℂ,
      riemannZeta (1 / 2 + s) = 0 →
        (¬ ∃ n : ℕ, 1 / 2 + s = -2 * (n + 1)) →
          (1 / 2 + s) ≠ 1 →
            s.re = 0 :=
  fun reserveDomination hBoundary =>
    finalRiemannHypothesis_centeredZeroCriterion_of_zetaWeilQuadraticPositivity
      (finalRiemannHypothesis_zetaWeilQuadraticPositivity_completedBoundary
        reserveDomination hBoundary)

theorem finalRiemannHypothesis_centeredZeroCriterion_of_logDerivControl
    (reserveDomination : FinalEndpointTraceReserveDomination)
    (hPhi : ∀ f : ZetaAdmissibleFunction,
      ZetaAdmissibleFunction.ZetaPhiAnalyticControl
        (ZetaAdmissibleFunction.convolutionAutocorrelation f))
    (hLog : ∀ f : ZetaAdmissibleFunction,
      ZetaAdmissibleFunction.CompletedZetaNegLogDerivControl
        (ZetaAdmissibleFunction.convolutionAutocorrelation f)) :
    ∀ s : ℂ,
      riemannZeta (1 / 2 + s) = 0 →
        (¬ ∃ n : ℕ, 1 / 2 + s = -2 * (n + 1)) →
          (1 / 2 + s) ≠ 1 →
            s.re = 0 :=
  finalRiemannHypothesis_centeredZeroCriterion
    reserveDomination
    (finalRiemannHypothesis_boundaryIdentification_of_logDerivControl hPhi hLog)

/-- The centered-zero criterion through the normalized-boundary route. -/
theorem finalRiemannHypothesis_centeredZeroCriterion_of_concreteLogDeriv_normalizedBoundary
    (hConcrete :
      ZetaAdmissibleFunction.CompletedZetaNegLogDerivAutocorrelationConcreteControl) :
    ∀ s : ℂ,
      riemannZeta (1 / 2 + s) = 0 →
        (¬ ∃ n : ℕ, 1 / 2 + s = -2 * (n + 1)) →
          (1 / 2 + s) ≠ 1 →
            s.re = 0 :=
  finalRiemannHypothesis_centeredZeroCriterion_of_zetaWeilQuadraticPositivity
    (finalRiemannHypothesis_zetaWeilQuadraticPositivity_of_concreteLogDeriv_normalizedBoundary
      hConcrete)

/-- Concrete completed-log-derivative control and canonical finite-residue
equality give the centered-zero criterion through raw Weil positivity. -/
theorem finalRiemannHypothesis_centeredZeroCriterion_of_concreteLogDeriv_canonicalGammaBinetFiniteResidueContourAssembly
    (hConcrete :
      ZetaAdmissibleFunction.CompletedZetaNegLogDerivAutocorrelationConcreteControl)
    (hGamma_slit : Complex.GammaRightHalfPlaneSlitPlaneControl)
    (hfinite : ZetaCompletedAutocorrelationScheduledFiniteResidueEquality) :
    ∀ s : ℂ,
      riemannZeta (1 / 2 + s) = 0 →
        (¬ ∃ n : ℕ, 1 / 2 + s = -2 * (n + 1)) →
          (1 / 2 + s) ≠ 1 →
            s.re = 0 :=
  finalRiemannHypothesis_centeredZeroCriterion_of_zetaWeilQuadraticPositivity
    (finalRiemannHypothesis_zetaWeilQuadraticPositivity_of_concreteLogDeriv_canonicalGammaBinetFiniteResidueContourAssembly
      hConcrete
      hGamma_slit
      hfinite)

/-- Concrete completed-log-derivative control and canonical pointwise
finite-rectangle residue equality give the centered-zero criterion through raw
Weil positivity. -/
theorem finalRiemannHypothesis_centeredZeroCriterion_of_concreteLogDeriv_canonicalGammaBinetPointwiseFiniteRectangleResidue
    (hConcrete :
      ZetaAdmissibleFunction.CompletedZetaNegLogDerivAutocorrelationConcreteControl)
    (hGamma_slit : Complex.GammaRightHalfPlaneSlitPlaneControl)
    (hfinite :
      ∀ f : ZetaAdmissibleFunction,
        ∀ hPhi : ZetaAdmissibleFunction.ZetaPhiAnalyticControl
          (ZetaAdmissibleFunction.convolutionAutocorrelation f),
        ∀ hLog : ZetaAdmissibleFunction.CompletedZetaNegLogDerivControl
          (ZetaAdmissibleFunction.convolutionAutocorrelation f),
        ∀ u : ℝ,
          ZetaAdmissibleFunction.zetaCompletedExplicitFormulaContourIntegral
              (ZetaAdmissibleFunction.convolutionAutocorrelation f)
              ((ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_contourFamily f).rectangle
                ((ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_familyAnalyticPackage
                  f
                  (ZetaAdmissibleFunction.zetaCompletedExplicitFormulaAutocorrelationHorizontalAvoidingSchedule f)
                  hPhi
                  hLog).height_schedule.height u)) =
            ZetaAdmissibleFunction.explicitFormulaCompletedZeroContourHeightWindowResidueSum
              (ZetaAdmissibleFunction.convolutionAutocorrelation f)
              ((ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_familyAnalyticPackage
                f
                (ZetaAdmissibleFunction.zetaCompletedExplicitFormulaAutocorrelationHorizontalAvoidingSchedule f)
                hPhi
                hLog).height_schedule.height u)) :
    ∀ s : ℂ,
      riemannZeta (1 / 2 + s) = 0 →
        (¬ ∃ n : ℕ, 1 / 2 + s = -2 * (n + 1)) →
          (1 / 2 + s) ≠ 1 →
            s.re = 0 :=
  finalRiemannHypothesis_centeredZeroCriterion_of_zetaWeilQuadraticPositivity
    (finalRiemannHypothesis_zetaWeilQuadraticPositivity_of_concreteLogDeriv_canonicalGammaBinetPointwiseFiniteRectangleResidue
      hConcrete
      hGamma_slit
      hfinite)

theorem finalRiemannHypothesis_centeredZeroCriterion_of_scheduledPackageBoundaryLimit
    (hScheduled :
      ∀ f : ZetaAdmissibleFunction,
        ZetaAdmissibleFunction.ExplicitFormulaScheduledFamilyAnalyticPackage
          (zetaAutocorrelationPhysicalProbe f)
          (zetaAutocorrelationPhysicalContourFamily f))
    (boundaryLimit :
      ∀ f : ZetaAdmissibleFunction,
        Tendsto
          (zetaAutocorrelationPhysicalScheduledPackagePoleCorrectedVertical
            f (hScheduled f))
          atTop
          (𝓝
            (zetaCompletedAffinePoleCorrectedBoundaryChannel
              (zetaAutocorrelationPhysicalProbe f)))) :
    ∀ s : ℂ,
      riemannZeta (1 / 2 + s) = 0 →
        (¬ ∃ n : ℕ, 1 / 2 + s = -2 * (n + 1)) →
          (1 / 2 + s) ≠ 1 →
            s.re = 0 :=
  finalRiemannHypothesis_centeredZeroCriterion_of_zetaWeilQuadraticPositivity
    (finalRiemannHypothesis_zetaWeilQuadraticPositivity_of_scheduledPackageBoundaryLimit
      hScheduled
      boundaryLimit)

theorem finalRiemannHypothesis_centeredZeroCriterion_of_completedBoundaryContourAssemblyOf
    (reserveDomination : FinalEndpointTraceReserveDomination)
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
    ∀ s : ℂ,
      riemannZeta (1 / 2 + s) = 0 →
        (¬ ∃ n : ℕ, 1 / 2 + s = -2 * (n + 1)) →
          (1 / 2 + s) ≠ 1 →
            s.re = 0 :=
  finalRiemannHypothesis_centeredZeroCriterion_completedBoundary
    reserveDomination
    (finalRiemannHypothesis_completedBoundaryIdentification_of_contourAssemblyOf
      schedule
      hPhi hLog hcoh hcontour)

theorem finalRiemannHypothesis_centeredZeroCriterion_of_finiteResidueContourAssemblyOf
    (reserveDomination : FinalEndpointTraceReserveDomination)
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
    (hGrowth : ∀ f : ZetaAdmissibleFunction,
      ZetaAdmissibleFunction.CompletedZetaNegLogDerivPolynomialGrowthControl
        (ZetaAdmissibleFunction.convolutionAutocorrelation f))
    (hcoh : Complex.gammaBinetPrincipalLogCoherence)
    (hfinite :
      ZetaCompletedAutocorrelationScheduledFiniteResidueEqualityOf schedule) :
    ∀ s : ℂ,
      riemannZeta (1 / 2 + s) = 0 →
        (¬ ∃ n : ℕ, 1 / 2 + s = -2 * (n + 1)) →
          (1 / 2 + s) ≠ 1 →
            s.re = 0 :=
  finalRiemannHypothesis_centeredZeroCriterion_of_completedBoundaryContourAssemblyOf
    reserveDomination
    schedule
    hPhi
    hLog
    hcoh
    (zetaCompletedAutocorrelationScheduledContourLimitOf_of_finiteResidueEquality_and_polynomialGrowthControl
      schedule
      hfinite
      hGrowth)

theorem finalRiemannHypothesis_centeredZeroCriterion_of_gammaBinetFiniteResidueContourAssemblyOf
    (reserveDomination : FinalEndpointTraceReserveDomination)
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
    (hGamma_slit : Complex.GammaRightHalfPlaneSlitPlaneControl)
    (hfiniteBinet : Complex.BinetAbelPlanaRightHalfPlaneFiniteDecomposition)
    (hfinite :
      ZetaCompletedAutocorrelationScheduledFiniteResidueEqualityOf schedule) :
    ∀ s : ℂ,
      riemannZeta (1 / 2 + s) = 0 →
        (¬ ∃ n : ℕ, 1 / 2 + s = -2 * (n + 1)) →
          (1 / 2 + s) ≠ 1 →
            s.re = 0 :=
  finalRiemannHypothesis_centeredZeroCriterion_of_finiteResidueContourAssemblyOf
    reserveDomination
    schedule
    hPhi
    hLog
    (ZetaAdmissibleFunction.completedZetaNegLogDerivPolynomialGrowthControl_autocorrelation_of_fullControl
      hLog)
    (Complex.gammaBinetPrincipalLogCoherence_of_ownerInputs
      hGamma_slit
      hfiniteBinet)
    hfinite

theorem finalRiemannHypothesis_centeredZeroCriterion_of_canonicalGammaBinetFiniteResidueContourAssemblyOf
    (reserveDomination : FinalEndpointTraceReserveDomination)
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
    (hGamma_slit : Complex.GammaRightHalfPlaneSlitPlaneControl)
    (hfinite :
      ZetaCompletedAutocorrelationScheduledFiniteResidueEqualityOf schedule) :
    ∀ s : ℂ,
      riemannZeta (1 / 2 + s) = 0 →
        (¬ ∃ n : ℕ, 1 / 2 + s = -2 * (n + 1)) →
          (1 / 2 + s) ≠ 1 →
            s.re = 0 :=
  finalRiemannHypothesis_centeredZeroCriterion_of_gammaBinetFiniteResidueContourAssemblyOf
    reserveDomination
    schedule
    hPhi
    hLog
    hGamma_slit
    Complex.binetAbelPlanaRightHalfPlaneFiniteDecomposition_owner
    hfinite

theorem finalRiemannHypothesis_centeredZeroCriterion_of_canonicalFiniteResidueContourAssembly
    (hPhi : ∀ f : ZetaAdmissibleFunction,
      ZetaAdmissibleFunction.ZetaPhiAnalyticControl
        (ZetaAdmissibleFunction.convolutionAutocorrelation f))
    (hLog : ∀ f : ZetaAdmissibleFunction,
      ZetaAdmissibleFunction.CompletedZetaNegLogDerivControl
        (ZetaAdmissibleFunction.convolutionAutocorrelation f))
    (hcoh : Complex.gammaBinetPrincipalLogCoherence)
    (hfinite : ZetaCompletedAutocorrelationScheduledFiniteResidueEquality) :
    ∀ s : ℂ,
      riemannZeta (1 / 2 + s) = 0 →
        (¬ ∃ n : ℕ, 1 / 2 + s = -2 * (n + 1)) →
          (1 / 2 + s) ≠ 1 →
            s.re = 0 :=
  finalRiemannHypothesis_centeredZeroCriterion_of_finiteResidueContourAssemblyOf
    finalRiemannHypothesis_endpointTraceReserveDomination_owner
    (fun f =>
      ZetaAdmissibleFunction.zetaCompletedExplicitFormulaAutocorrelationHorizontalAvoidingSchedule
        f)
    hPhi
    hLog
    (ZetaAdmissibleFunction.completedZetaNegLogDerivPolynomialGrowthControl_autocorrelation_of_fullControl
      hLog)
    hcoh
    hfinite

theorem finalRiemannHypothesis_centeredZeroCriterion_of_canonicalGammaBinetFiniteResidueContourAssembly
    (hPhi : ∀ f : ZetaAdmissibleFunction,
      ZetaAdmissibleFunction.ZetaPhiAnalyticControl
        (ZetaAdmissibleFunction.convolutionAutocorrelation f))
    (hLog : ∀ f : ZetaAdmissibleFunction,
      ZetaAdmissibleFunction.CompletedZetaNegLogDerivControl
        (ZetaAdmissibleFunction.convolutionAutocorrelation f))
    (hGamma_slit : Complex.GammaRightHalfPlaneSlitPlaneControl)
    (hfinite : ZetaCompletedAutocorrelationScheduledFiniteResidueEquality) :
    ∀ s : ℂ,
      riemannZeta (1 / 2 + s) = 0 →
        (¬ ∃ n : ℕ, 1 / 2 + s = -2 * (n + 1)) →
          (1 / 2 + s) ≠ 1 →
            s.re = 0 :=
  finalRiemannHypothesis_centeredZeroCriterion_of_canonicalGammaBinetFiniteResidueContourAssemblyOf
    finalRiemannHypothesis_endpointTraceReserveDomination_owner
    (fun f =>
      ZetaAdmissibleFunction.zetaCompletedExplicitFormulaAutocorrelationHorizontalAvoidingSchedule
        f)
    hPhi
    hLog
    hGamma_slit
    hfinite

end
end LFunctions
end Boundary
