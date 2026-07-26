import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaZeroKreinGram.WeilCriterion.OwnerParts.CanonicalScheduleCompatibility
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaCompletedLogDerivativeControl.PolynomialGrowthControl
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaCompletedLogDerivativeControl.GlobalCauchyFactorData
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.GammaBinetStirling.CoherenceComponents
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaAdmissibleTransformRegularity.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaZeroKreinGram.WeilCriterion.OwnerParts.EndpointReservePositivity

/-!
# Canonical completed-boundary positivity assembly

This owner part keeps the final positivity lane in the completed-boundary
coordinate from contour assembly, then uses the endpoint physical
absorption owner to pass to raw Weil positivity.
-/

namespace Boundary
namespace LFunctions

noncomputable section

/-- Canonical contour assembly gives the completed-boundary identification from
height-window residue equality and polynomial completed-log-derivative growth. -/
theorem zetaWeilAutocorrelationCompletedBoundaryIdentification_of_canonicalHeightWindowResidueEquality
    (hPhi :
      ∀ f : ZetaAdmissibleFunction,
        ZetaAdmissibleFunction.ZetaPhiAnalyticControl
          (ZetaAdmissibleFunction.convolutionAutocorrelation f))
    (hLog :
      ∀ f : ZetaAdmissibleFunction,
        ZetaAdmissibleFunction.CompletedZetaNegLogDerivControl
          (ZetaAdmissibleFunction.convolutionAutocorrelation f))
    (hcoh : Complex.gammaBinetPrincipalLogCoherence)
    (hheight : ZetaCompletedAutocorrelationCanonicalHeightWindowResidueEquality)
    (hGrowth :
      ∀ f : ZetaAdmissibleFunction,
        ZetaAdmissibleFunction.CompletedZetaNegLogDerivPolynomialGrowthControl
          (ZetaAdmissibleFunction.convolutionAutocorrelation f)) :
    ZetaWeilAutocorrelationCompletedBoundaryIdentification :=
  zetaWeilAutocorrelationCompletedBoundaryIdentification_of_contourAssembly
    hPhi
    hLog
    hcoh
    (zetaCompletedAutocorrelationScheduledContourLimit_of_heightWindowResidueEquality_and_polynomialGrowthControl
      hheight
      hGrowth)

/-- Completed-boundary identification gives raw Weil positivity through the
canonical endpoint physical absorption theorem. -/
theorem zetaWeilQuadraticPositivity_of_completedBoundaryIdentification_endpointPhysicalAbsorption_owner
    (boundaryIdentification :
      ZetaWeilAutocorrelationCompletedBoundaryIdentification) :
    ZetaWeilQuadraticPositivity :=
  zetaWeilQuadraticPositivity_of_endpointAbsorbedPhysical_completedBoundary_owner
    boundaryIdentification
    (fun f =>
      ZetaAdmissibleFunction.completedWeilEndpointAbsorbedPhysicalScalar_nonnegative_owner
        f)

/-- Canonical contour assembly inputs give raw Weil positivity in the
completed-boundary lane. -/
theorem zetaWeilQuadraticPositivity_of_canonicalCompletedBoundaryContourAssembly_owner
    (hPhi :
      ∀ f : ZetaAdmissibleFunction,
        ZetaAdmissibleFunction.ZetaPhiAnalyticControl
          (ZetaAdmissibleFunction.convolutionAutocorrelation f))
    (hLog :
      ∀ f : ZetaAdmissibleFunction,
        ZetaAdmissibleFunction.CompletedZetaNegLogDerivControl
          (ZetaAdmissibleFunction.convolutionAutocorrelation f))
    (hcoh : Complex.gammaBinetPrincipalLogCoherence)
    (hheight : ZetaCompletedAutocorrelationCanonicalHeightWindowResidueEquality)
    (hGrowth :
      ∀ f : ZetaAdmissibleFunction,
        ZetaAdmissibleFunction.CompletedZetaNegLogDerivPolynomialGrowthControl
          (ZetaAdmissibleFunction.convolutionAutocorrelation f)) :
    ZetaWeilQuadraticPositivity :=
  zetaWeilQuadraticPositivity_of_completedBoundaryIdentification_endpointPhysicalAbsorption_owner
    (zetaWeilAutocorrelationCompletedBoundaryIdentification_of_canonicalHeightWindowResidueEquality
      hPhi
      hLog
      hcoh
      hheight
      hGrowth)

/-- Canonical finite-residue equality and polynomial growth give the
completed-boundary identification through the scheduled contour assembly. -/
theorem zetaWeilAutocorrelationCompletedBoundaryIdentification_of_canonicalFiniteResidueEquality
    (hPhi :
      ∀ f : ZetaAdmissibleFunction,
        ZetaAdmissibleFunction.ZetaPhiAnalyticControl
          (ZetaAdmissibleFunction.convolutionAutocorrelation f))
    (hLog :
      ∀ f : ZetaAdmissibleFunction,
        ZetaAdmissibleFunction.CompletedZetaNegLogDerivControl
          (ZetaAdmissibleFunction.convolutionAutocorrelation f))
    (hcoh : Complex.gammaBinetPrincipalLogCoherence)
    (hfinite : ZetaCompletedAutocorrelationScheduledFiniteResidueEquality)
    (hGrowth :
      ∀ f : ZetaAdmissibleFunction,
        ZetaAdmissibleFunction.CompletedZetaNegLogDerivPolynomialGrowthControl
          (ZetaAdmissibleFunction.convolutionAutocorrelation f)) :
    ZetaWeilAutocorrelationCompletedBoundaryIdentification :=
  zetaWeilAutocorrelationCompletedBoundaryIdentification_of_contourAssembly
    hPhi
    hLog
    hcoh
    (zetaCompletedAutocorrelationScheduledContourLimit_of_finiteResidueEquality_and_polynomialGrowthControl
      hfinite
      hGrowth)

/-- Canonical finite-residue equality and polynomial growth give raw Weil
positivity through the completed-boundary contour lane. -/
theorem zetaWeilQuadraticPositivity_of_canonicalCompletedBoundaryFiniteResidueAssembly_owner
    (hPhi :
      ∀ f : ZetaAdmissibleFunction,
        ZetaAdmissibleFunction.ZetaPhiAnalyticControl
          (ZetaAdmissibleFunction.convolutionAutocorrelation f))
    (hLog :
      ∀ f : ZetaAdmissibleFunction,
        ZetaAdmissibleFunction.CompletedZetaNegLogDerivControl
          (ZetaAdmissibleFunction.convolutionAutocorrelation f))
    (hcoh : Complex.gammaBinetPrincipalLogCoherence)
    (hfinite : ZetaCompletedAutocorrelationScheduledFiniteResidueEquality)
    (hGrowth :
      ∀ f : ZetaAdmissibleFunction,
        ZetaAdmissibleFunction.CompletedZetaNegLogDerivPolynomialGrowthControl
          (ZetaAdmissibleFunction.convolutionAutocorrelation f)) :
    ZetaWeilQuadraticPositivity :=
  zetaWeilQuadraticPositivity_of_completedBoundaryIdentification_endpointPhysicalAbsorption_owner
    (zetaWeilAutocorrelationCompletedBoundaryIdentification_of_canonicalFiniteResidueEquality
      hPhi
      hLog
      hcoh
      hfinite
      hGrowth)

/-- Full autocorrelation log-derivative control supplies the polynomial growth
control needed in the canonical contour-limit assembly. -/
theorem completedZetaNegLogDerivPolynomialGrowthControl_autocorrelation_of_logDerivControl_owner
    (hLog :
      ∀ f : ZetaAdmissibleFunction,
        ZetaAdmissibleFunction.CompletedZetaNegLogDerivControl
          (ZetaAdmissibleFunction.convolutionAutocorrelation f)) :
    ∀ f : ZetaAdmissibleFunction,
      ZetaAdmissibleFunction.CompletedZetaNegLogDerivPolynomialGrowthControl
        (ZetaAdmissibleFunction.convolutionAutocorrelation f) :=
  ZetaAdmissibleFunction.completedZetaNegLogDerivPolynomialGrowthControl_autocorrelation_of_fullControl
    hLog

/-- Canonical contour assembly inputs give raw Weil positivity; polynomial
growth is derived from the same full log-derivative control. -/
theorem zetaWeilQuadraticPositivity_of_canonicalCompletedBoundaryContourAssembly_logDerivControl_owner
    (hPhi :
      ∀ f : ZetaAdmissibleFunction,
        ZetaAdmissibleFunction.ZetaPhiAnalyticControl
          (ZetaAdmissibleFunction.convolutionAutocorrelation f))
    (hLog :
      ∀ f : ZetaAdmissibleFunction,
        ZetaAdmissibleFunction.CompletedZetaNegLogDerivControl
          (ZetaAdmissibleFunction.convolutionAutocorrelation f))
    (hcoh : Complex.gammaBinetPrincipalLogCoherence)
    (hheight : ZetaCompletedAutocorrelationCanonicalHeightWindowResidueEquality) :
    ZetaWeilQuadraticPositivity :=
  zetaWeilQuadraticPositivity_of_canonicalCompletedBoundaryContourAssembly_owner
    hPhi
    hLog
    hcoh
    hheight
    (completedZetaNegLogDerivPolynomialGrowthControl_autocorrelation_of_logDerivControl_owner
      hLog)

/-- Canonical finite-residue equality and full log-derivative control give raw
Weil positivity; polynomial growth is derived from the same log-derivative
control. -/
theorem zetaWeilQuadraticPositivity_of_canonicalCompletedBoundaryFiniteResidueAssembly_logDerivControl_owner
    (hPhi :
      ∀ f : ZetaAdmissibleFunction,
        ZetaAdmissibleFunction.ZetaPhiAnalyticControl
          (ZetaAdmissibleFunction.convolutionAutocorrelation f))
    (hLog :
      ∀ f : ZetaAdmissibleFunction,
        ZetaAdmissibleFunction.CompletedZetaNegLogDerivControl
          (ZetaAdmissibleFunction.convolutionAutocorrelation f))
    (hcoh : Complex.gammaBinetPrincipalLogCoherence)
    (hfinite : ZetaCompletedAutocorrelationScheduledFiniteResidueEquality) :
    ZetaWeilQuadraticPositivity :=
  zetaWeilQuadraticPositivity_of_canonicalCompletedBoundaryFiniteResidueAssembly_owner
    hPhi
    hLog
    hcoh
    hfinite
    (completedZetaNegLogDerivPolynomialGrowthControl_autocorrelation_of_logDerivControl_owner
      hLog)

/-- The canonical autocorrelation transform control supplies the `Phi` input
for the completed-boundary contour assembly. -/
theorem zetaPhiAnalyticControl_autocorrelation_canonical_owner :
    ∀ f : ZetaAdmissibleFunction,
      ZetaAdmissibleFunction.ZetaPhiAnalyticControl
        (ZetaAdmissibleFunction.convolutionAutocorrelation f) :=
  ZetaAdmissibleFunction.zetaPhiAnalyticControl_autocorrelation_of_concreteControl
    ZetaAdmissibleFunction.zetaPhiAutocorrelationConcreteControl_owner

/-- Canonical transform control plus full log-derivative control give raw Weil
positivity through the completed-boundary contour lane. -/
theorem zetaWeilQuadraticPositivity_of_canonicalPhi_completedBoundaryContourAssembly_logDerivControl_owner
    (hLog :
      ∀ f : ZetaAdmissibleFunction,
        ZetaAdmissibleFunction.CompletedZetaNegLogDerivControl
          (ZetaAdmissibleFunction.convolutionAutocorrelation f))
    (hcoh : Complex.gammaBinetPrincipalLogCoherence)
    (hheight : ZetaCompletedAutocorrelationCanonicalHeightWindowResidueEquality) :
    ZetaWeilQuadraticPositivity :=
  zetaWeilQuadraticPositivity_of_canonicalCompletedBoundaryContourAssembly_logDerivControl_owner
    zetaPhiAnalyticControl_autocorrelation_canonical_owner
    hLog
    hcoh
    hheight

/-- Canonical transform control and full log-derivative control give raw Weil
positivity from the canonical finite-residue equality package. -/
theorem zetaWeilQuadraticPositivity_of_canonicalPhi_completedBoundaryFiniteResidueAssembly_logDerivControl_owner
    (hLog :
      ∀ f : ZetaAdmissibleFunction,
        ZetaAdmissibleFunction.CompletedZetaNegLogDerivControl
          (ZetaAdmissibleFunction.convolutionAutocorrelation f))
    (hcoh : Complex.gammaBinetPrincipalLogCoherence)
    (hfinite : ZetaCompletedAutocorrelationScheduledFiniteResidueEquality) :
    ZetaWeilQuadraticPositivity :=
  zetaWeilQuadraticPositivity_of_canonicalCompletedBoundaryFiniteResidueAssembly_logDerivControl_owner
    zetaPhiAnalyticControl_autocorrelation_canonical_owner
    hLog
    hcoh
    hfinite

/-- Canonical residue-error vanishing gives the height-window equality consumed
in the completed-boundary contour lane. -/
theorem zetaCompletedAutocorrelationCanonicalHeightWindowResidueEquality_of_residueErrorVanishing_owner
    (hzero : ZetaCompletedAutocorrelationCanonicalResidueEqualityErrorVanishing) :
    ZetaCompletedAutocorrelationCanonicalHeightWindowResidueEquality :=
  zetaCompletedAutocorrelationCanonicalHeightWindowResidueEquality_of_residueEqualityErrorVanishing
    hzero

/-- Canonical transform control and full log-derivative control give raw Weil
positivity from the residue-error vanishing owner target. -/
theorem zetaWeilQuadraticPositivity_of_canonicalPhi_completedBoundaryContourAssembly_residueErrorVanishing_owner
    (hLog :
      ∀ f : ZetaAdmissibleFunction,
        ZetaAdmissibleFunction.CompletedZetaNegLogDerivControl
          (ZetaAdmissibleFunction.convolutionAutocorrelation f))
    (hcoh : Complex.gammaBinetPrincipalLogCoherence)
    (hzero : ZetaCompletedAutocorrelationCanonicalResidueEqualityErrorVanishing) :
    ZetaWeilQuadraticPositivity :=
  zetaWeilQuadraticPositivity_of_canonicalPhi_completedBoundaryContourAssembly_logDerivControl_owner
    hLog
    hcoh
    (zetaCompletedAutocorrelationCanonicalHeightWindowResidueEquality_of_residueErrorVanishing_owner
      hzero)

/-- The canonical finite Abel-Plana decomposition and Gamma slit-plane theorem
assemble the Binet principal-log coherence input. -/
theorem gammaBinetPrincipalLogCoherence_of_canonicalFinite_owner
    (hGammaSlit : Complex.GammaRightHalfPlaneSlitPlaneControl) :
    Complex.gammaBinetPrincipalLogCoherence :=
  Complex.gammaBinetPrincipalLogCoherence_of_ownerInputs
    hGammaSlit
    Complex.binetAbelPlanaRightHalfPlaneFiniteDecomposition_owner

/-- Canonical transform control, full log-derivative control, finite Abel-Plana
control, and residue-error vanishing give raw Weil positivity. -/
theorem zetaWeilQuadraticPositivity_of_canonicalPhi_completedBoundaryContourAssembly_gammaSlit_residueErrorVanishing_owner
    (hLog :
      ∀ f : ZetaAdmissibleFunction,
        ZetaAdmissibleFunction.CompletedZetaNegLogDerivControl
          (ZetaAdmissibleFunction.convolutionAutocorrelation f))
    (hGammaSlit : Complex.GammaRightHalfPlaneSlitPlaneControl)
    (hzero : ZetaCompletedAutocorrelationCanonicalResidueEqualityErrorVanishing) :
    ZetaWeilQuadraticPositivity :=
  zetaWeilQuadraticPositivity_of_canonicalPhi_completedBoundaryContourAssembly_residueErrorVanishing_owner
    hLog
    (gammaBinetPrincipalLogCoherence_of_canonicalFinite_owner
      hGammaSlit)
    hzero

/-- Canonical transform control, full log-derivative control, finite Abel-Plana
control, and finite-residue equality give raw Weil positivity. -/
theorem zetaWeilQuadraticPositivity_of_canonicalPhi_completedBoundaryFiniteResidueAssembly_gammaSlit_owner
    (hLog :
      ∀ f : ZetaAdmissibleFunction,
        ZetaAdmissibleFunction.CompletedZetaNegLogDerivControl
          (ZetaAdmissibleFunction.convolutionAutocorrelation f))
    (hGammaSlit : Complex.GammaRightHalfPlaneSlitPlaneControl)
    (hfinite : ZetaCompletedAutocorrelationScheduledFiniteResidueEquality) :
    ZetaWeilQuadraticPositivity :=
  zetaWeilQuadraticPositivity_of_canonicalPhi_completedBoundaryFiniteResidueAssembly_logDerivControl_owner
    hLog
    (gammaBinetPrincipalLogCoherence_of_canonicalFinite_owner
      hGammaSlit)
    hfinite

/-- Concrete autocorrelation completed-log-derivative control supplies the full
log-derivative input for the completed-boundary contour lane. -/
theorem completedZetaNegLogDerivControl_autocorrelation_of_concreteControl_owner
    (hConcrete :
      ZetaAdmissibleFunction.CompletedZetaNegLogDerivAutocorrelationConcreteControl) :
    ∀ f : ZetaAdmissibleFunction,
      ZetaAdmissibleFunction.CompletedZetaNegLogDerivControl
        (ZetaAdmissibleFunction.convolutionAutocorrelation f) :=
  ZetaAdmissibleFunction.completedZetaNegLogDerivControl_autocorrelation_of_concreteControl
    hConcrete

/-- Concrete autocorrelation log-derivative control, finite Abel-Plana control,
Gamma slit-plane control, and residue-error vanishing give raw Weil positivity
through the completed-boundary contour lane. -/
theorem zetaWeilQuadraticPositivity_of_canonicalPhi_completedBoundaryContourAssembly_concreteLogDeriv_gammaSlit_residueErrorVanishing_owner
    (hConcrete :
      ZetaAdmissibleFunction.CompletedZetaNegLogDerivAutocorrelationConcreteControl)
    (hGammaSlit : Complex.GammaRightHalfPlaneSlitPlaneControl)
    (hzero : ZetaCompletedAutocorrelationCanonicalResidueEqualityErrorVanishing) :
    ZetaWeilQuadraticPositivity :=
  zetaWeilQuadraticPositivity_of_canonicalPhi_completedBoundaryContourAssembly_gammaSlit_residueErrorVanishing_owner
    (completedZetaNegLogDerivControl_autocorrelation_of_concreteControl_owner
      hConcrete)
    hGammaSlit
    hzero

/-- Concrete autocorrelation log-derivative control, Gamma slit-plane control,
and canonical height-window residue equality give raw Weil positivity through
the completed-boundary contour lane. -/
theorem zetaWeilQuadraticPositivity_of_canonicalPhi_completedBoundaryContourAssembly_concreteLogDeriv_gammaSlit_heightWindowResidueEquality_owner
    (hConcrete :
      ZetaAdmissibleFunction.CompletedZetaNegLogDerivAutocorrelationConcreteControl)
    (hGammaSlit : Complex.GammaRightHalfPlaneSlitPlaneControl)
    (hheight : ZetaCompletedAutocorrelationCanonicalHeightWindowResidueEquality) :
    ZetaWeilQuadraticPositivity :=
  zetaWeilQuadraticPositivity_of_canonicalPhi_completedBoundaryContourAssembly_concreteLogDeriv_gammaSlit_residueErrorVanishing_owner
    hConcrete
    hGammaSlit
    (zetaCompletedAutocorrelationCanonicalResidueEqualityErrorVanishing_of_heightWindowResidueEquality
      hheight)

/-- Concrete autocorrelation log-derivative control, finite Abel-Plana control,
Gamma slit-plane control, and finite-residue equality give raw Weil positivity
through the completed-boundary contour lane. -/
theorem zetaWeilQuadraticPositivity_of_canonicalPhi_completedBoundaryFiniteResidueAssembly_concreteLogDeriv_gammaSlit_owner
    (hConcrete :
      ZetaAdmissibleFunction.CompletedZetaNegLogDerivAutocorrelationConcreteControl)
    (hGammaSlit : Complex.GammaRightHalfPlaneSlitPlaneControl)
    (hfinite : ZetaCompletedAutocorrelationScheduledFiniteResidueEquality) :
    ZetaWeilQuadraticPositivity :=
  zetaWeilQuadraticPositivity_of_canonicalPhi_completedBoundaryFiniteResidueAssembly_gammaSlit_owner
    (completedZetaNegLogDerivControl_autocorrelation_of_concreteControl_owner
      hConcrete)
    hGammaSlit
    hfinite

/-- Factor-bound data supplies the completed-log-derivative input for the
completed-boundary contour lane. -/
theorem completedZetaNegLogDerivControl_autocorrelation_of_factorBoundData_for_completedBoundary_owner
    (data :
      ∀ (a b : ℝ) (E : CompletedZetaZeroExcisedStrip a b),
        CompletedZetaZeroExcisedStrip.FactorBoundData E) :
    ∀ f : ZetaAdmissibleFunction,
      ZetaAdmissibleFunction.CompletedZetaNegLogDerivControl
        (ZetaAdmissibleFunction.convolutionAutocorrelation f) :=
  ZetaAdmissibleFunction.completedZetaNegLogDerivControl_autocorrelation_of_factorBoundData_owner
    data

/-- Direct logarithmic-derivative packages supply the same completed-boundary
input without introducing Cauchy-circle magnitude estimates. -/
theorem completedZetaNegLogDerivControl_autocorrelation_of_globalLogDeriv_for_completedBoundary_owner
    (zetaData :
      ∀ (a b : ℝ) (E : CompletedZetaZeroExcisedStrip a b),
        CompletedZetaZeroExcisedStrip.ZetaSideBoundData E)
    (gammaData :
      ∀ (a b : ℝ) (E : CompletedZetaZeroExcisedStrip a b),
        CompletedZetaZeroExcisedStrip.InverseGammaBoundData E) :
    ∀ f : ZetaAdmissibleFunction,
      ZetaAdmissibleFunction.CompletedZetaNegLogDerivControl
        (ZetaAdmissibleFunction.convolutionAutocorrelation f) :=
  completedZetaNegLogDerivControl_autocorrelation_of_factorBoundData_for_completedBoundary_owner
    (CompletedZetaZeroExcisedStrip.factorBoundData_of_globalLogDeriv_owner
      zetaData gammaData)

/-- Global Cauchy log-derivative estimates supply the completed-boundary
contour lane's completed-log-derivative input. -/
theorem completedZetaNegLogDerivControl_autocorrelation_of_globalCauchyLogDerivative_for_completedBoundary_owner
    (separated :
      ∀ (a b : ℝ) (E : CompletedZetaZeroExcisedStrip a b),
        E.HasPositiveSingularSeparation)
    (zetaRadius zetaAmplitude zetaValueLower :
      ∀ (a b : ℝ) (E : CompletedZetaZeroExcisedStrip a b), ℕ → ℝ)
    (gammaRadius gammaAmplitude gammaValueLower :
      ∀ (a b : ℝ) (E : CompletedZetaZeroExcisedStrip a b), ℕ → ℝ)
    (zetaRadius_pos :
      ∀ (a b : ℝ) (E : CompletedZetaZeroExcisedStrip a b)
        (N : ℕ),
        0 < zetaRadius a b E N)
    (zetaAmplitude_pos :
      ∀ (a b : ℝ) (E : CompletedZetaZeroExcisedStrip a b)
        (N : ℕ),
        0 < zetaAmplitude a b E N)
    (zetaValueLower_pos :
      ∀ (a b : ℝ) (E : CompletedZetaZeroExcisedStrip a b)
        (N : ℕ),
        0 < zetaValueLower a b E N)
    (gammaRadius_pos :
      ∀ (a b : ℝ) (E : CompletedZetaZeroExcisedStrip a b)
        (N : ℕ),
        0 < gammaRadius a b E N)
    (gammaAmplitude_pos :
      ∀ (a b : ℝ) (E : CompletedZetaZeroExcisedStrip a b)
        (N : ℕ),
        0 < gammaAmplitude a b E N)
    (gammaValueLower_pos :
      ∀ (a b : ℝ) (E : CompletedZetaZeroExcisedStrip a b)
        (N : ℕ),
        0 < gammaValueLower a b E N)
    (zetaDiffCont :
      ∀ (a b : ℝ) (E : CompletedZetaZeroExcisedStrip a b)
        (N : ℕ) (z : ℂ),
        z ∈ E.carrier →
        DiffContOnCl ℂ zetaSideFactor
          (Metric.ball z (zetaRadius a b E N)))
    (zetaSphereBound :
      ∀ (a b : ℝ) (E : CompletedZetaZeroExcisedStrip a b)
        (N : ℕ) (z : ℂ),
        z ∈ E.carrier →
        ∀ w : ℂ,
          w ∈ Metric.sphere z (zetaRadius a b E N) →
          ‖zetaSideFactor w‖ ≤
            zetaAmplitude a b E N * (1 + ‖z.im‖) ^ N)
    (zetaValueLower_bound :
      ∀ (a b : ℝ) (E : CompletedZetaZeroExcisedStrip a b)
        (N : ℕ) (z : ℂ),
        z ∈ E.carrier →
        zetaValueLower a b E N ≤ ‖zetaSideFactor z‖)
    (gammaDiffCont :
      ∀ (a b : ℝ) (E : CompletedZetaZeroExcisedStrip a b)
        (N : ℕ) (z : ℂ),
        z ∈ E.carrier →
        DiffContOnCl ℂ
          (fun w : ℂ => (Complex.Gammaℝ w)⁻¹)
          (Metric.ball z (gammaRadius a b E N)))
    (gammaSphereBound :
      ∀ (a b : ℝ) (E : CompletedZetaZeroExcisedStrip a b)
        (N : ℕ) (z : ℂ),
        z ∈ E.carrier →
        ∀ w : ℂ,
          w ∈ Metric.sphere z (gammaRadius a b E N) →
          ‖(Complex.Gammaℝ w)⁻¹‖ ≤
            gammaAmplitude a b E N * (1 + ‖z.im‖) ^ N)
    (gammaValueLower_bound :
      ∀ (a b : ℝ) (E : CompletedZetaZeroExcisedStrip a b)
        (N : ℕ) (z : ℂ),
        z ∈ E.carrier →
        gammaValueLower a b E N ≤ ‖(Complex.Gammaℝ z)⁻¹‖) :
    ∀ f : ZetaAdmissibleFunction,
      ZetaAdmissibleFunction.CompletedZetaNegLogDerivControl
        (ZetaAdmissibleFunction.convolutionAutocorrelation f) :=
  completedZetaNegLogDerivControl_autocorrelation_of_factorBoundData_for_completedBoundary_owner
    (ZetaAdmissibleFunction.CompletedZetaZeroExcisedStrip.factorBoundData_of_globalCauchyLogDerivative_owner
      separated
      zetaRadius
      zetaAmplitude
      zetaValueLower
      gammaRadius
      gammaAmplitude
      gammaValueLower
      zetaRadius_pos
      zetaAmplitude_pos
      zetaValueLower_pos
      gammaRadius_pos
      gammaAmplitude_pos
      gammaValueLower_pos
      zetaDiffCont
      zetaSphereBound
      zetaValueLower_bound
      gammaDiffCont
      gammaSphereBound
      gammaValueLower_bound)

/-- Factor-bound data, finite Abel-Plana control, Gamma slit-plane control, and
residue-error vanishing give raw Weil positivity through the completed-boundary
contour lane. -/
theorem zetaWeilQuadraticPositivity_of_canonicalPhi_completedBoundaryContourAssembly_factorBoundData_gammaSlit_residueErrorVanishing_owner
    (data :
      ∀ (a b : ℝ) (E : CompletedZetaZeroExcisedStrip a b),
        CompletedZetaZeroExcisedStrip.FactorBoundData E)
    (hGammaSlit : Complex.GammaRightHalfPlaneSlitPlaneControl)
    (hzero : ZetaCompletedAutocorrelationCanonicalResidueEqualityErrorVanishing) :
    ZetaWeilQuadraticPositivity :=
  zetaWeilQuadraticPositivity_of_canonicalPhi_completedBoundaryContourAssembly_gammaSlit_residueErrorVanishing_owner
    (completedZetaNegLogDerivControl_autocorrelation_of_factorBoundData_for_completedBoundary_owner
      data)
    hGammaSlit
    hzero

/-- Factor-bound data, finite Abel-Plana control, Gamma slit-plane control, and
height-window residue equality give raw Weil positivity through the
completed-boundary contour lane. -/
theorem zetaWeilQuadraticPositivity_of_canonicalPhi_completedBoundaryContourAssembly_factorBoundData_gammaSlit_heightWindowResidueEquality_owner
    (data :
      ∀ (a b : ℝ) (E : CompletedZetaZeroExcisedStrip a b),
        CompletedZetaZeroExcisedStrip.FactorBoundData E)
    (hGammaSlit : Complex.GammaRightHalfPlaneSlitPlaneControl)
    (hfinite : ZetaCompletedAutocorrelationCanonicalHeightWindowResidueEquality) :
    ZetaWeilQuadraticPositivity :=
  zetaWeilQuadraticPositivity_of_canonicalPhi_completedBoundaryContourAssembly_factorBoundData_gammaSlit_residueErrorVanishing_owner
    data
    hGammaSlit
    (zetaCompletedAutocorrelationCanonicalResidueEqualityErrorVanishing_of_heightWindowResidueEquality
      hfinite)

/-- Factor-bound data, finite Abel-Plana control, Gamma slit-plane control, and
finite-residue equality give raw Weil positivity through the completed-boundary
contour lane. -/
theorem zetaWeilQuadraticPositivity_of_canonicalPhi_completedBoundaryFiniteResidueAssembly_factorBoundData_gammaSlit_owner
    (data :
      ∀ (a b : ℝ) (E : CompletedZetaZeroExcisedStrip a b),
        CompletedZetaZeroExcisedStrip.FactorBoundData E)
    (hGammaSlit : Complex.GammaRightHalfPlaneSlitPlaneControl)
    (hfinite : ZetaCompletedAutocorrelationScheduledFiniteResidueEquality) :
    ZetaWeilQuadraticPositivity :=
  zetaWeilQuadraticPositivity_of_canonicalPhi_completedBoundaryFiniteResidueAssembly_gammaSlit_owner
    (completedZetaNegLogDerivControl_autocorrelation_of_factorBoundData_for_completedBoundary_owner
      data)
    hGammaSlit
    hfinite

end

end LFunctions
end Boundary
