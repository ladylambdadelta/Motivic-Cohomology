import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaCompletedLogDerivativeControl.GlobalCauchyFactorData
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaZeroKreinGram.WeilCriterion.OwnerParts.SuppliedScheduleCarrierCanonicalAssembly

/-!
# Supplied-schedule factor-control assembly

This file peels the global completed-log-derivative factor-control input in the
supplied-schedule positivity lane into the concrete `FactorBoundData` object
from the completed-log-derivative control layer.
-/

namespace Boundary
namespace LFunctions

noncomputable section

/-- Canonical carrier Cauchy positivity from concrete global factor-bound data. -/
theorem zetaWeilQuadraticPositivity_of_canonicalScheduledCarrierCauchyPackage_factorBoundData_traceBessel_owner
    (K : ZetaAdmissibleFunction → ℕ)
    (carrierData : CanonicalScheduledCarrierCauchyData K)
    (factorData :
      ∀ (a b : ℝ) (E : ZetaAdmissibleFunction.CompletedZetaZeroExcisedStrip a b),
        ZetaAdmissibleFunction.CompletedZetaZeroExcisedStrip.FactorBoundData E) :
    ZetaWeilQuadraticPositivity :=
  zetaWeilQuadraticPositivity_of_canonicalScheduledCarrierCauchyPackage_globalFactorControls_traceBessel_owner
    K
    carrierData
    (ZetaAdmissibleFunction.CompletedZetaNegLogDerivZetaSideControl.ofFactorBoundData
      factorData)
    (ZetaAdmissibleFunction.CompletedZetaNegLogDerivInverseGammaControl.ofFactorBoundData
      factorData)

/-- Scalar carrier Cauchy estimates and concrete global factor-bound data give
canonical carrier positivity. -/
theorem zetaWeilQuadraticPositivity_of_canonicalScheduledCarrierScalarCauchyData_factorBoundData_traceBessel_owner
    (K : ZetaAdmissibleFunction → ℕ)
    (zetaRadius zetaAmplitude zetaValueLower :
      ∀ f : ZetaAdmissibleFunction, ℝ)
    (gammaRadius gammaAmplitude gammaValueLower :
      ∀ f : ZetaAdmissibleFunction, ℝ)
    (zetaRadius_pos :
      ∀ f : ZetaAdmissibleFunction, 0 < zetaRadius f)
    (zetaAmplitude_pos :
      ∀ f : ZetaAdmissibleFunction, 0 < zetaAmplitude f)
    (zetaValueLower_pos :
      ∀ f : ZetaAdmissibleFunction, 0 < zetaValueLower f)
    (gammaRadius_pos :
      ∀ f : ZetaAdmissibleFunction, 0 < gammaRadius f)
    (gammaAmplitude_pos :
      ∀ f : ZetaAdmissibleFunction, 0 < gammaAmplitude f)
    (gammaValueLower_pos :
      ∀ f : ZetaAdmissibleFunction, 0 < gammaValueLower f)
    (zetaDiffCont :
      ∀ (f : ZetaAdmissibleFunction) (z : ℂ),
        z ∈
          (ZetaAdmissibleFunction.zetaCompletedExplicitFormulaAutocorrelationScheduledHorizontalCarrier
            f).carrier →
        DiffContOnCl ℂ ZetaAdmissibleFunction.zetaSideFactor
          (Metric.ball z (zetaRadius f)))
    (gammaDiffCont :
      ∀ (f : ZetaAdmissibleFunction) (z : ℂ),
        z ∈
          (ZetaAdmissibleFunction.zetaCompletedExplicitFormulaAutocorrelationScheduledHorizontalCarrier
            f).carrier →
        DiffContOnCl ℂ
          (fun w : ℂ => (Complex.Gammaℝ w)⁻¹)
          (Metric.ball z (gammaRadius f)))
    (zetaSphereBound :
      ∀ (f : ZetaAdmissibleFunction) (z : ℂ),
        z ∈
          (ZetaAdmissibleFunction.zetaCompletedExplicitFormulaAutocorrelationScheduledHorizontalCarrier
            f).carrier →
        ∀ w : ℂ,
          w ∈ Metric.sphere z (zetaRadius f) →
          ‖ZetaAdmissibleFunction.zetaSideFactor w‖ ≤
            zetaAmplitude f * (1 + ‖z.im‖) ^ K f)
    (gammaSphereBound :
      ∀ (f : ZetaAdmissibleFunction) (z : ℂ),
        z ∈
          (ZetaAdmissibleFunction.zetaCompletedExplicitFormulaAutocorrelationScheduledHorizontalCarrier
            f).carrier →
        ∀ w : ℂ,
          w ∈ Metric.sphere z (gammaRadius f) →
          ‖(Complex.Gammaℝ w)⁻¹‖ ≤
            gammaAmplitude f * (1 + ‖z.im‖) ^ K f)
    (zetaValueLower_bound :
      ∀ (f : ZetaAdmissibleFunction) (z : ℂ),
        z ∈
          (ZetaAdmissibleFunction.zetaCompletedExplicitFormulaAutocorrelationScheduledHorizontalCarrier
            f).carrier →
        zetaValueLower f ≤ ‖ZetaAdmissibleFunction.zetaSideFactor z‖)
    (gammaValueLower_bound :
      ∀ (f : ZetaAdmissibleFunction) (z : ℂ),
        z ∈
          (ZetaAdmissibleFunction.zetaCompletedExplicitFormulaAutocorrelationScheduledHorizontalCarrier
            f).carrier →
        gammaValueLower f ≤ ‖(Complex.Gammaℝ z)⁻¹‖)
    (factorData :
      ∀ (a b : ℝ) (E : ZetaAdmissibleFunction.CompletedZetaZeroExcisedStrip a b),
        ZetaAdmissibleFunction.CompletedZetaZeroExcisedStrip.FactorBoundData E) :
    ZetaWeilQuadraticPositivity :=
  zetaWeilQuadraticPositivity_of_canonicalScheduledCarrierCauchyPackage_factorBoundData_traceBessel_owner
    K
    { zetaRadius := zetaRadius
      zetaAmplitude := zetaAmplitude
      zetaValueLower := zetaValueLower
      gammaRadius := gammaRadius
      gammaAmplitude := gammaAmplitude
      gammaValueLower := gammaValueLower
      zetaRadius_pos := zetaRadius_pos
      zetaAmplitude_pos := zetaAmplitude_pos
      zetaValueLower_pos := zetaValueLower_pos
      gammaRadius_pos := gammaRadius_pos
      gammaAmplitude_pos := gammaAmplitude_pos
      gammaValueLower_pos := gammaValueLower_pos
      zetaDiffCont := zetaDiffCont
      gammaDiffCont := gammaDiffCont
      zetaSphereBound := zetaSphereBound
      gammaSphereBound := gammaSphereBound
      zetaValueLower_bound := zetaValueLower_bound
      gammaValueLower_bound := gammaValueLower_bound }
    factorData

/-- Scalar carrier Cauchy estimates and global Cauchy factor estimates give
canonical carrier positivity. -/
theorem zetaWeilQuadraticPositivity_of_canonicalScheduledCarrierScalarCauchyData_globalCauchyFactorData_traceBessel_owner
    (K : ZetaAdmissibleFunction → ℕ)
    (zetaRadius zetaAmplitude zetaValueLower :
      ∀ f : ZetaAdmissibleFunction, ℝ)
    (gammaRadius gammaAmplitude gammaValueLower :
      ∀ f : ZetaAdmissibleFunction, ℝ)
    (zetaRadius_pos :
      ∀ f : ZetaAdmissibleFunction, 0 < zetaRadius f)
    (zetaAmplitude_pos :
      ∀ f : ZetaAdmissibleFunction, 0 < zetaAmplitude f)
    (zetaValueLower_pos :
      ∀ f : ZetaAdmissibleFunction, 0 < zetaValueLower f)
    (gammaRadius_pos :
      ∀ f : ZetaAdmissibleFunction, 0 < gammaRadius f)
    (gammaAmplitude_pos :
      ∀ f : ZetaAdmissibleFunction, 0 < gammaAmplitude f)
    (gammaValueLower_pos :
      ∀ f : ZetaAdmissibleFunction, 0 < gammaValueLower f)
    (zetaDiffCont :
      ∀ (f : ZetaAdmissibleFunction) (z : ℂ),
        z ∈
          (ZetaAdmissibleFunction.zetaCompletedExplicitFormulaAutocorrelationScheduledHorizontalCarrier
            f).carrier →
        DiffContOnCl ℂ ZetaAdmissibleFunction.zetaSideFactor
          (Metric.ball z (zetaRadius f)))
    (gammaDiffCont :
      ∀ (f : ZetaAdmissibleFunction) (z : ℂ),
        z ∈
          (ZetaAdmissibleFunction.zetaCompletedExplicitFormulaAutocorrelationScheduledHorizontalCarrier
            f).carrier →
        DiffContOnCl ℂ
          (fun w : ℂ => (Complex.Gammaℝ w)⁻¹)
          (Metric.ball z (gammaRadius f)))
    (zetaSphereBound :
      ∀ (f : ZetaAdmissibleFunction) (z : ℂ),
        z ∈
          (ZetaAdmissibleFunction.zetaCompletedExplicitFormulaAutocorrelationScheduledHorizontalCarrier
            f).carrier →
        ∀ w : ℂ,
          w ∈ Metric.sphere z (zetaRadius f) →
          ‖ZetaAdmissibleFunction.zetaSideFactor w‖ ≤
            zetaAmplitude f * (1 + ‖z.im‖) ^ K f)
    (gammaSphereBound :
      ∀ (f : ZetaAdmissibleFunction) (z : ℂ),
        z ∈
          (ZetaAdmissibleFunction.zetaCompletedExplicitFormulaAutocorrelationScheduledHorizontalCarrier
            f).carrier →
        ∀ w : ℂ,
          w ∈ Metric.sphere z (gammaRadius f) →
          ‖(Complex.Gammaℝ w)⁻¹‖ ≤
            gammaAmplitude f * (1 + ‖z.im‖) ^ K f)
    (zetaValueLower_bound :
      ∀ (f : ZetaAdmissibleFunction) (z : ℂ),
        z ∈
          (ZetaAdmissibleFunction.zetaCompletedExplicitFormulaAutocorrelationScheduledHorizontalCarrier
            f).carrier →
        zetaValueLower f ≤ ‖ZetaAdmissibleFunction.zetaSideFactor z‖)
    (gammaValueLower_bound :
      ∀ (f : ZetaAdmissibleFunction) (z : ℂ),
        z ∈
          (ZetaAdmissibleFunction.zetaCompletedExplicitFormulaAutocorrelationScheduledHorizontalCarrier
            f).carrier →
        gammaValueLower f ≤ ‖(Complex.Gammaℝ z)⁻¹‖)
    (separated :
      ∀ (a b : ℝ) (E : ZetaAdmissibleFunction.CompletedZetaZeroExcisedStrip a b),
        E.HasPositiveSingularSeparation)
    (globalZetaRadius globalZetaAmplitude globalZetaValueLower :
      ∀ (a b : ℝ)
        (E : ZetaAdmissibleFunction.CompletedZetaZeroExcisedStrip a b), ℕ → ℝ)
    (globalGammaRadius globalGammaAmplitude globalGammaValueLower :
      ∀ (a b : ℝ)
        (E : ZetaAdmissibleFunction.CompletedZetaZeroExcisedStrip a b), ℕ → ℝ)
    (globalZetaRadius_pos :
      ∀ (a b : ℝ)
        (E : ZetaAdmissibleFunction.CompletedZetaZeroExcisedStrip a b)
        (N : ℕ),
        0 < globalZetaRadius a b E N)
    (globalZetaAmplitude_pos :
      ∀ (a b : ℝ)
        (E : ZetaAdmissibleFunction.CompletedZetaZeroExcisedStrip a b)
        (N : ℕ),
        0 < globalZetaAmplitude a b E N)
    (globalZetaValueLower_pos :
      ∀ (a b : ℝ)
        (E : ZetaAdmissibleFunction.CompletedZetaZeroExcisedStrip a b)
        (N : ℕ),
        0 < globalZetaValueLower a b E N)
    (globalGammaRadius_pos :
      ∀ (a b : ℝ)
        (E : ZetaAdmissibleFunction.CompletedZetaZeroExcisedStrip a b)
        (N : ℕ),
        0 < globalGammaRadius a b E N)
    (globalGammaAmplitude_pos :
      ∀ (a b : ℝ)
        (E : ZetaAdmissibleFunction.CompletedZetaZeroExcisedStrip a b)
        (N : ℕ),
        0 < globalGammaAmplitude a b E N)
    (globalGammaValueLower_pos :
      ∀ (a b : ℝ)
        (E : ZetaAdmissibleFunction.CompletedZetaZeroExcisedStrip a b)
        (N : ℕ),
        0 < globalGammaValueLower a b E N)
    (globalZetaDiffCont :
      ∀ (a b : ℝ)
        (E : ZetaAdmissibleFunction.CompletedZetaZeroExcisedStrip a b)
        (N : ℕ) (z : ℂ),
        z ∈ E.carrier →
        DiffContOnCl ℂ ZetaAdmissibleFunction.zetaSideFactor
          (Metric.ball z (globalZetaRadius a b E N)))
    (globalZetaSphereBound :
      ∀ (a b : ℝ)
        (E : ZetaAdmissibleFunction.CompletedZetaZeroExcisedStrip a b)
        (N : ℕ) (z : ℂ),
        z ∈ E.carrier →
        ∀ w : ℂ,
          w ∈ Metric.sphere z (globalZetaRadius a b E N) →
          ‖ZetaAdmissibleFunction.zetaSideFactor w‖ ≤
            globalZetaAmplitude a b E N * (1 + ‖z.im‖) ^ N)
    (globalZetaValueLower_bound :
      ∀ (a b : ℝ)
        (E : ZetaAdmissibleFunction.CompletedZetaZeroExcisedStrip a b)
        (N : ℕ) (z : ℂ),
        z ∈ E.carrier →
        globalZetaValueLower a b E N ≤
          ‖ZetaAdmissibleFunction.zetaSideFactor z‖)
    (globalGammaDiffCont :
      ∀ (a b : ℝ)
        (E : ZetaAdmissibleFunction.CompletedZetaZeroExcisedStrip a b)
        (N : ℕ) (z : ℂ),
        z ∈ E.carrier →
        DiffContOnCl ℂ
          (fun w : ℂ => (Complex.Gammaℝ w)⁻¹)
          (Metric.ball z (globalGammaRadius a b E N)))
    (globalGammaSphereBound :
      ∀ (a b : ℝ)
        (E : ZetaAdmissibleFunction.CompletedZetaZeroExcisedStrip a b)
        (N : ℕ) (z : ℂ),
        z ∈ E.carrier →
        ∀ w : ℂ,
          w ∈ Metric.sphere z (globalGammaRadius a b E N) →
          ‖(Complex.Gammaℝ w)⁻¹‖ ≤
            globalGammaAmplitude a b E N * (1 + ‖z.im‖) ^ N)
    (globalGammaValueLower_bound :
      ∀ (a b : ℝ)
        (E : ZetaAdmissibleFunction.CompletedZetaZeroExcisedStrip a b)
        (N : ℕ) (z : ℂ),
        z ∈ E.carrier →
        globalGammaValueLower a b E N ≤ ‖(Complex.Gammaℝ z)⁻¹‖) :
    ZetaWeilQuadraticPositivity :=
  zetaWeilQuadraticPositivity_of_canonicalScheduledCarrierScalarCauchyData_factorBoundData_traceBessel_owner
    K
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
    gammaDiffCont
    zetaSphereBound
    gammaSphereBound
    zetaValueLower_bound
    gammaValueLower_bound
    (ZetaAdmissibleFunction.CompletedZetaZeroExcisedStrip.factorBoundData_of_globalCauchyLogDerivative_owner
      separated
      globalZetaRadius
      globalZetaAmplitude
      globalZetaValueLower
      globalGammaRadius
      globalGammaAmplitude
      globalGammaValueLower
      globalZetaRadius_pos
      globalZetaAmplitude_pos
      globalZetaValueLower_pos
      globalGammaRadius_pos
      globalGammaAmplitude_pos
      globalGammaValueLower_pos
      globalZetaDiffCont
      globalZetaSphereBound
      globalZetaValueLower_bound
      globalGammaDiffCont
      globalGammaSphereBound
      globalGammaValueLower_bound)

/-- Supplied carrier-family positivity from concrete global factor-bound data. -/
theorem zetaWeilQuadraticPositivity_of_suppliedCarrierFamily_factorBoundData_traceBessel_owner
    (carrierFamily :
      ZetaAdmissibleFunction.SuppliedScheduleCarrierCauchyFamily)
    (factorData :
      ∀ (a b : ℝ) (E : ZetaAdmissibleFunction.CompletedZetaZeroExcisedStrip a b),
        ZetaAdmissibleFunction.CompletedZetaZeroExcisedStrip.FactorBoundData E) :
    ZetaWeilQuadraticPositivity :=
  zetaWeilQuadraticPositivity_of_suppliedCarrierFamily_globalFactorControls_traceBessel_owner
    carrierFamily
    (ZetaAdmissibleFunction.CompletedZetaNegLogDerivZetaSideControl.ofFactorBoundData
      factorData)
    (ZetaAdmissibleFunction.CompletedZetaNegLogDerivInverseGammaControl.ofFactorBoundData
      factorData)

/-- Canonical supplied-schedule positivity from canonical carrier Cauchy data,
canonical carrier separation, canonical Phi control, and concrete global
factor-bound data. -/
theorem zetaWeilQuadraticPositivity_of_canonicalScheduledCarrierCauchyPackage_suppliedSchedule_canonicalPhi_factorBoundData_traceBessel_owner
    (K : ZetaAdmissibleFunction → ℕ)
    (carrierData : CanonicalScheduledCarrierCauchyData K)
    (separated :
      ∀ f : ZetaAdmissibleFunction,
        (ZetaAdmissibleFunction.zetaCompletedExplicitFormulaAutocorrelationScheduledHorizontalCarrier
          f).HasPositiveSingularSeparation)
    (factorData :
      ∀ (a b : ℝ) (E : ZetaAdmissibleFunction.CompletedZetaZeroExcisedStrip a b),
        ZetaAdmissibleFunction.CompletedZetaZeroExcisedStrip.FactorBoundData E) :
    ZetaWeilQuadraticPositivity :=
  zetaWeilQuadraticPositivity_of_canonicalScheduledCarrierCauchyPackage_suppliedSchedule_canonicalPhi_globalFactorControls_traceBessel_owner
    K
    carrierData
    separated
    (ZetaAdmissibleFunction.CompletedZetaNegLogDerivZetaSideControl.ofFactorBoundData
      factorData)
    (ZetaAdmissibleFunction.CompletedZetaNegLogDerivInverseGammaControl.ofFactorBoundData
      factorData)

/-- Canonical supplied-schedule positivity from canonical carrier Cauchy data,
an explicit Phi-control family, canonical carrier separation, and concrete
global factor-bound data. -/
theorem zetaWeilQuadraticPositivity_of_canonicalScheduledCarrierCauchyPackage_suppliedSchedule_factorBoundData_traceBessel_owner
    (K : ZetaAdmissibleFunction → ℕ)
    (carrierData : CanonicalScheduledCarrierCauchyData K)
    (separated :
      ∀ f : ZetaAdmissibleFunction,
        (ZetaAdmissibleFunction.zetaCompletedExplicitFormulaAutocorrelationScheduledHorizontalCarrier
          f).HasPositiveSingularSeparation)
    (hPhi :
      ∀ f : ZetaAdmissibleFunction,
        ZetaAdmissibleFunction.ZetaPhiAnalyticControl
          (ZetaAdmissibleFunction.convolutionAutocorrelation f))
    (factorData :
      ∀ (a b : ℝ) (E : ZetaAdmissibleFunction.CompletedZetaZeroExcisedStrip a b),
        ZetaAdmissibleFunction.CompletedZetaZeroExcisedStrip.FactorBoundData E) :
    ZetaWeilQuadraticPositivity :=
  zetaWeilQuadraticPositivity_of_canonicalScheduledCarrierCauchyPackage_suppliedSchedule_globalFactorControls_traceBessel_owner
    K
    carrierData
    separated
    hPhi
    (ZetaAdmissibleFunction.CompletedZetaNegLogDerivZetaSideControl.ofFactorBoundData
      factorData)
    (ZetaAdmissibleFunction.CompletedZetaNegLogDerivInverseGammaControl.ofFactorBoundData
      factorData)

end

end LFunctions
end Boundary
