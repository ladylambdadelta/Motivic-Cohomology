import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.OwnerParts.FinalCriteria

namespace Boundary
namespace LFunctions

noncomputable section

open Filter
open scoped Topology

theorem boundaryRiemannHypothesis_of_boundaryIdentification_owner
    (reserveDomination : FinalEndpointTraceReserveDomination)
    (hBoundary : ZetaWeilAutocorrelationBoundaryIdentification) :
    boundaryRiemannHypothesis :=
  boundaryRiemannHypothesis_of_centeredZeroCriterion
    (finalRiemannHypothesis_centeredZeroCriterion reserveDomination hBoundary)

theorem boundaryRiemannHypothesis_completedBoundary_owner
    (reserveDomination : FinalEndpointTraceReserveDomination)
    (hBoundary : ZetaWeilAutocorrelationCompletedBoundaryIdentification) :
    boundaryRiemannHypothesis :=
  boundaryRiemannHypothesis_of_centeredZeroCriterion
    (finalRiemannHypothesis_centeredZeroCriterion_completedBoundary
      reserveDomination hBoundary)

theorem boundaryRiemannHypothesis_of_zeroSideBoundaryIdentification_owner
    (reserveDomination : FinalEndpointTraceReserveDomination)
    (zeroBoundary :
      ZetaCompletedAutocorrelationZeroSideBoundaryIdentification) :
    boundaryRiemannHypothesis :=
  boundaryRiemannHypothesis_of_boundaryIdentification_owner
    reserveDomination
    (zetaWeilAutocorrelationBoundaryIdentification_of_zeroSideBoundaryIdentification_core
      zeroBoundary)

theorem boundaryRiemannHypothesis_of_poleCorrectedCommonLimit_owner
    (reserveDomination : FinalEndpointTraceReserveDomination)
    (commonLimit :
      ZetaCompletedAutocorrelationPoleCorrectedCommonLimit) :
    boundaryRiemannHypothesis :=
  boundaryRiemannHypothesis_of_zeroSideBoundaryIdentification_owner
    reserveDomination
    (zetaCompletedAutocorrelationZeroSideBoundaryIdentification_of_commonLimit_core
      commonLimit)

theorem boundaryRiemannHypothesis_of_logDerivControl_owner
    (reserveDomination : FinalEndpointTraceReserveDomination)
    (hPhi : ∀ f : ZetaAdmissibleFunction,
      ZetaAdmissibleFunction.ZetaPhiAnalyticControl
        (ZetaAdmissibleFunction.convolutionAutocorrelation f))
    (hLog : ∀ f : ZetaAdmissibleFunction,
      ZetaAdmissibleFunction.CompletedZetaNegLogDerivControl
        (ZetaAdmissibleFunction.convolutionAutocorrelation f)) :
    boundaryRiemannHypothesis :=
  boundaryRiemannHypothesis_of_poleCorrectedCommonLimit_owner
    reserveDomination
    (zetaCompletedAutocorrelationPoleCorrectedCommonLimit_of_logDerivControl_scheduledPackage
      hPhi hLog)

theorem boundaryRiemannHypothesis_of_logDerivBoundaryIdentification_owner
    (reserveDomination : FinalEndpointTraceReserveDomination)
    (hPhi : ∀ f : ZetaAdmissibleFunction,
      ZetaAdmissibleFunction.ZetaPhiAnalyticControl
        (ZetaAdmissibleFunction.convolutionAutocorrelation f))
    (hLog : ∀ f : ZetaAdmissibleFunction,
      ZetaAdmissibleFunction.CompletedZetaNegLogDerivControl
        (ZetaAdmissibleFunction.convolutionAutocorrelation f)) :
    boundaryRiemannHypothesis :=
  boundaryRiemannHypothesis_of_boundaryIdentification_owner
    reserveDomination
    (finalRiemannHypothesis_boundaryIdentification_of_logDerivControl hPhi hLog)

/-- Concrete completed-log-derivative control and canonical finite-residue
equality give the Boundary RH statement through the completed-boundary
finite-residue lane. -/
theorem boundaryRiemannHypothesis_of_concreteLogDeriv_canonicalGammaBinetFiniteResidueContourAssembly_owner
    (hConcrete :
      ZetaAdmissibleFunction.CompletedZetaNegLogDerivAutocorrelationConcreteControl)
    (hGamma_slit : Complex.GammaRightHalfPlaneSlitPlaneControl)
    (hfinite : ZetaCompletedAutocorrelationScheduledFiniteResidueEquality) :
    boundaryRiemannHypothesis :=
  boundaryRiemannHypothesis_of_centeredZeroCriterion
    (finalRiemannHypothesis_centeredZeroCriterion_of_concreteLogDeriv_canonicalGammaBinetFiniteResidueContourAssembly
      hConcrete
      hGamma_slit
      hfinite)

/-- Concrete completed-log-derivative control and canonical height-window
residue equality give the Boundary RH statement through the
completed-boundary contour lane. -/
theorem boundaryRiemannHypothesis_of_concreteLogDeriv_canonicalGammaBinetHeightWindowResidueContourAssembly_owner
    (hConcrete :
      ZetaAdmissibleFunction.CompletedZetaNegLogDerivAutocorrelationConcreteControl)
    (hGamma_slit : Complex.GammaRightHalfPlaneSlitPlaneControl)
    (hheight : ZetaCompletedAutocorrelationCanonicalHeightWindowResidueEquality) :
    boundaryRiemannHypothesis :=
  boundaryRiemannHypothesis_of_centeredZeroCriterion
    (finalRiemannHypothesis_centeredZeroCriterion_of_concreteLogDeriv_canonicalGammaBinetHeightWindowResidueContourAssembly
      hConcrete
      hGamma_slit
      hheight)

theorem boundaryRiemannHypothesis_of_completedBoundaryContourAssemblyOf_owner
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
    boundaryRiemannHypothesis :=
  boundaryRiemannHypothesis_completedBoundary_owner
    reserveDomination
    (finalRiemannHypothesis_completedBoundaryIdentification_of_contourAssemblyOf
      schedule
      hPhi hLog hcoh hcontour)

theorem boundaryRiemannHypothesis_of_finiteResidueContourAssemblyOf_owner
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
    boundaryRiemannHypothesis :=
  boundaryRiemannHypothesis_of_completedBoundaryContourAssemblyOf_owner
    reserveDomination
    schedule
    hPhi
    hLog
    hcoh
    (zetaCompletedAutocorrelationScheduledContourLimitOf_of_finiteResidueEquality_and_polynomialGrowthControl
      schedule
      hfinite
      hGrowth)

theorem boundaryRiemannHypothesis_of_gammaBinetFiniteResidueContourAssemblyOf_owner
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
    boundaryRiemannHypothesis :=
  boundaryRiemannHypothesis_of_finiteResidueContourAssemblyOf_owner
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

theorem boundaryRiemannHypothesis_of_canonicalGammaBinetFiniteResidueContourAssemblyOf_owner
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
    boundaryRiemannHypothesis :=
  boundaryRiemannHypothesis_of_gammaBinetFiniteResidueContourAssemblyOf_owner
    reserveDomination
    schedule
    hPhi
    hLog
    hGamma_slit
    Complex.binetAbelPlanaRightHalfPlaneFiniteDecomposition_owner
    hfinite

theorem boundaryRiemannHypothesis_of_canonicalFiniteResidueContourAssembly_owner
    (hPhi : ∀ f : ZetaAdmissibleFunction,
      ZetaAdmissibleFunction.ZetaPhiAnalyticControl
        (ZetaAdmissibleFunction.convolutionAutocorrelation f))
    (hLog : ∀ f : ZetaAdmissibleFunction,
      ZetaAdmissibleFunction.CompletedZetaNegLogDerivControl
        (ZetaAdmissibleFunction.convolutionAutocorrelation f))
    (hcoh : Complex.gammaBinetPrincipalLogCoherence)
    (hfinite : ZetaCompletedAutocorrelationScheduledFiniteResidueEquality) :
    boundaryRiemannHypothesis :=
  boundaryRiemannHypothesis_of_finiteResidueContourAssemblyOf_owner
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

theorem boundaryRiemannHypothesis_of_canonicalGammaBinetFiniteResidueContourAssembly_owner
    (hPhi : ∀ f : ZetaAdmissibleFunction,
      ZetaAdmissibleFunction.ZetaPhiAnalyticControl
        (ZetaAdmissibleFunction.convolutionAutocorrelation f))
    (hLog : ∀ f : ZetaAdmissibleFunction,
      ZetaAdmissibleFunction.CompletedZetaNegLogDerivControl
        (ZetaAdmissibleFunction.convolutionAutocorrelation f))
    (hGamma_slit : Complex.GammaRightHalfPlaneSlitPlaneControl)
    (hfinite : ZetaCompletedAutocorrelationScheduledFiniteResidueEquality) :
    boundaryRiemannHypothesis :=
  boundaryRiemannHypothesis_of_canonicalGammaBinetFiniteResidueContourAssemblyOf_owner
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
