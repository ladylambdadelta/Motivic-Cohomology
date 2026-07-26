import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaZeroKreinGram.WeilCriterion.OwnerParts.FinalCarrierCauchyConcreteAssembly
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaZeroKreinGram.WeilCriterion.OwnerParts.CanonicalCarrierCauchyFactorData
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaCompletedLogDerivativeControl.FactorBoundDataOwner
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaCompletedLogDerivativeControl.GlobalCauchyFactorData

/-!
# Final carrier-factor assembly

This owner part connects canonical scheduled-carrier factor data directly to the
final common-limit lane.  It keeps the carrier-factor route separate from the
larger carrier-Cauchy data package.
-/

namespace Boundary
namespace LFunctions

noncomputable section

def canonicalScheduledCarrierFactorData_of_globalFactorBoundData_final_owner
    (factorData :
      ∀ (a b : ℝ) (E : ZetaAdmissibleFunction.CompletedZetaZeroExcisedStrip a b),
        ZetaAdmissibleFunction.CompletedZetaZeroExcisedStrip.FactorBoundData E)
    (f : ZetaAdmissibleFunction) :
    ZetaAdmissibleFunction.CompletedZetaZeroExcisedStrip.FactorBoundData
      (ZetaAdmissibleFunction.zetaCompletedExplicitFormulaAutocorrelationScheduledHorizontalCarrier
        f) :=
  factorData
    (min
      (ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c
      (1 -
        (ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c))
    (max
      (ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c
      (1 -
        (ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c))
    (ZetaAdmissibleFunction.zetaCompletedExplicitFormulaAutocorrelationScheduledHorizontalCarrier
      f)

/-- Canonical scheduled-carrier factor data and affine packet data construct
the corrected pole-corrected common limit. -/
theorem zetaCompletedAutocorrelationPoleCorrectedCommonLimit_of_canonicalScheduledCarrierFactorData_affinePacketData_final_owner
    (factorData :
      ∀ f : ZetaAdmissibleFunction,
        ZetaAdmissibleFunction.CompletedZetaZeroExcisedStrip.FactorBoundData
          (ZetaAdmissibleFunction.zetaCompletedExplicitFormulaAutocorrelationScheduledHorizontalCarrier f))
    (packetData :
      ∀ f : ZetaAdmissibleFunction,
        ZetaAdmissibleFunction.ZetaCompletedAutocorrelationAffinePacketData f) :
    ZetaCompletedAutocorrelationPoleCorrectedCommonLimit :=
  zetaCompletedAutocorrelationPoleCorrectedCommonLimit_of_polynomialScheduledAffinePacketData_final_owner
    (fun f =>
      ZetaAdmissibleFunction.zetaCompletedExplicitFormulaAutocorrelationScheduledPolynomialFamilyAnalyticPackage_of_carrierFactorData
        f
        ((ZetaAdmissibleFunction.zetaPhiAnalyticControl_autocorrelation_of_concreteControl
          ZetaAdmissibleFunction.zetaPhiAutocorrelationConcreteControl_owner) f)
        (factorData f))
    packetData

/-- Canonical scheduled-carrier factor data and concrete autocorrelation
completed-log-derivative control construct the corrected pole-corrected common
limit. -/
theorem zetaCompletedAutocorrelationPoleCorrectedCommonLimit_of_canonicalScheduledCarrierFactorData_concreteControl_final_owner
    (factorData :
      ∀ f : ZetaAdmissibleFunction,
        ZetaAdmissibleFunction.CompletedZetaZeroExcisedStrip.FactorBoundData
          (ZetaAdmissibleFunction.zetaCompletedExplicitFormulaAutocorrelationScheduledHorizontalCarrier f))
    (hConcrete :
      ZetaAdmissibleFunction.CompletedZetaNegLogDerivAutocorrelationConcreteControl) :
    ZetaCompletedAutocorrelationPoleCorrectedCommonLimit :=
  zetaCompletedAutocorrelationPoleCorrectedCommonLimit_of_canonicalScheduledCarrierFactorData_affinePacketData_final_owner
    factorData
    (fun f =>
      ZetaAdmissibleFunction.zetaCompletedAutocorrelationAffinePacketData_of_concreteControl_owner
        f
        hConcrete)

/-- Canonical scheduled-carrier factor data and split autocorrelation factor
controls construct the corrected pole-corrected common limit. -/
theorem zetaCompletedAutocorrelationPoleCorrectedCommonLimit_of_canonicalScheduledCarrierFactorData_splitControls_final_owner
    (factorData :
      ∀ f : ZetaAdmissibleFunction,
        ZetaAdmissibleFunction.CompletedZetaZeroExcisedStrip.FactorBoundData
          (ZetaAdmissibleFunction.zetaCompletedExplicitFormulaAutocorrelationScheduledHorizontalCarrier f))
    (hZetaSide :
      ZetaAdmissibleFunction.CompletedZetaNegLogDerivAutocorrelationZetaSideControl)
    (hInverseGamma :
      ZetaAdmissibleFunction.CompletedZetaNegLogDerivAutocorrelationInverseGammaControl) :
    ZetaCompletedAutocorrelationPoleCorrectedCommonLimit :=
  zetaCompletedAutocorrelationPoleCorrectedCommonLimit_of_canonicalScheduledCarrierFactorData_concreteControl_final_owner
    factorData
    (ZetaAdmissibleFunction.completedZetaNegLogDerivAutocorrelationConcreteControl_of_factorControls
      hZetaSide
      hInverseGamma)

/-- Canonical scheduled-carrier factor data and global factor controls construct
the corrected pole-corrected common limit. -/
theorem zetaCompletedAutocorrelationPoleCorrectedCommonLimit_of_canonicalScheduledCarrierFactorData_globalFactorControls_final_owner
    (factorData :
      ∀ f : ZetaAdmissibleFunction,
        ZetaAdmissibleFunction.CompletedZetaZeroExcisedStrip.FactorBoundData
          (ZetaAdmissibleFunction.zetaCompletedExplicitFormulaAutocorrelationScheduledHorizontalCarrier f))
    (hZetaSide :
      ZetaAdmissibleFunction.CompletedZetaNegLogDerivZetaSideControl)
    (hInverseGamma :
      ZetaAdmissibleFunction.CompletedZetaNegLogDerivInverseGammaControl) :
    ZetaCompletedAutocorrelationPoleCorrectedCommonLimit :=
  zetaCompletedAutocorrelationPoleCorrectedCommonLimit_of_canonicalScheduledCarrierFactorData_splitControls_final_owner
    factorData
    (ZetaAdmissibleFunction.CompletedZetaNegLogDerivAutocorrelationZetaSideControl.ofZetaSideControl
      hZetaSide)
    (ZetaAdmissibleFunction.CompletedZetaNegLogDerivAutocorrelationInverseGammaControl.ofInverseGammaControl
      hInverseGamma)

theorem zetaCompletedAutocorrelationPoleCorrectedCommonLimit_of_globalFactorBoundData_final_owner
    (factorData :
      ∀ (a b : ℝ) (E : ZetaAdmissibleFunction.CompletedZetaZeroExcisedStrip a b),
        ZetaAdmissibleFunction.CompletedZetaZeroExcisedStrip.FactorBoundData E) :
    ZetaCompletedAutocorrelationPoleCorrectedCommonLimit :=
  zetaCompletedAutocorrelationPoleCorrectedCommonLimit_of_canonicalScheduledCarrierFactorData_concreteControl_final_owner
    (canonicalScheduledCarrierFactorData_of_globalFactorBoundData_final_owner
      factorData)
    (ZetaAdmissibleFunction.completedZetaNegLogDerivAutocorrelationConcreteControl_of_factorBoundData_owner
      factorData)

theorem zetaWeilQuadraticPositivity_of_globalFactorBoundData_final_owner
    (factorData :
      ∀ (a b : ℝ) (E : ZetaAdmissibleFunction.CompletedZetaZeroExcisedStrip a b),
        ZetaAdmissibleFunction.CompletedZetaZeroExcisedStrip.FactorBoundData E) :
    ZetaWeilQuadraticPositivity :=
  zetaWeilQuadraticPositivity_of_finalCommonLimit_owner
    (zetaCompletedAutocorrelationPoleCorrectedCommonLimit_of_globalFactorBoundData_final_owner
      factorData)

/-- Direct logarithmic-derivative owner packages feed the final positivity
assembly without passing through the Cauchy-data layer. -/
theorem zetaWeilQuadraticPositivity_of_globalLogDerivFactorData_final_owner
    (zetaData :
      ∀ (a b : ℝ)
        (E : ZetaAdmissibleFunction.CompletedZetaZeroExcisedStrip a b),
        ZetaAdmissibleFunction.CompletedZetaZeroExcisedStrip.ZetaSideBoundData E)
    (gammaData :
      ∀ (a b : ℝ)
        (E : ZetaAdmissibleFunction.CompletedZetaZeroExcisedStrip a b),
        ZetaAdmissibleFunction.CompletedZetaZeroExcisedStrip.InverseGammaBoundData E) :
    ZetaWeilQuadraticPositivity :=
  zetaWeilQuadraticPositivity_of_globalFactorBoundData_final_owner
    (ZetaAdmissibleFunction.CompletedZetaZeroExcisedStrip.factorBoundData_of_globalLogDeriv_owner
      zetaData gammaData)

theorem zetaWeilQuadraticPositivity_of_globalCauchyFactorData_final_owner
    (separated :
      ∀ (a b : ℝ)
        (E : ZetaAdmissibleFunction.CompletedZetaZeroExcisedStrip a b),
        E.HasPositiveSingularSeparation)
    (zetaRadius zetaAmplitude zetaValueLower :
      ∀ (a b : ℝ)
        (E : ZetaAdmissibleFunction.CompletedZetaZeroExcisedStrip a b),
        ℕ → ℝ)
    (gammaRadius gammaAmplitude gammaValueLower :
      ∀ (a b : ℝ)
        (E : ZetaAdmissibleFunction.CompletedZetaZeroExcisedStrip a b),
        ℕ → ℝ)
    (zetaRadius_pos :
      ∀ (a b : ℝ)
        (E : ZetaAdmissibleFunction.CompletedZetaZeroExcisedStrip a b)
        (N : ℕ),
        0 < zetaRadius a b E N)
    (zetaAmplitude_pos :
      ∀ (a b : ℝ)
        (E : ZetaAdmissibleFunction.CompletedZetaZeroExcisedStrip a b)
        (N : ℕ),
        0 < zetaAmplitude a b E N)
    (zetaValueLower_pos :
      ∀ (a b : ℝ)
        (E : ZetaAdmissibleFunction.CompletedZetaZeroExcisedStrip a b)
        (N : ℕ),
        0 < zetaValueLower a b E N)
    (gammaRadius_pos :
      ∀ (a b : ℝ)
        (E : ZetaAdmissibleFunction.CompletedZetaZeroExcisedStrip a b)
        (N : ℕ),
        0 < gammaRadius a b E N)
    (gammaAmplitude_pos :
      ∀ (a b : ℝ)
        (E : ZetaAdmissibleFunction.CompletedZetaZeroExcisedStrip a b)
        (N : ℕ),
        0 < gammaAmplitude a b E N)
    (gammaValueLower_pos :
      ∀ (a b : ℝ)
        (E : ZetaAdmissibleFunction.CompletedZetaZeroExcisedStrip a b)
        (N : ℕ),
        0 < gammaValueLower a b E N)
    (zetaDiffCont :
      ∀ (a b : ℝ)
        (E : ZetaAdmissibleFunction.CompletedZetaZeroExcisedStrip a b)
        (N : ℕ) (z : ℂ),
        z ∈ E.carrier →
          DiffContOnCl ℂ ZetaAdmissibleFunction.zetaSideFactor
            (Metric.ball z (zetaRadius a b E N)))
    (zetaSphereBound :
      ∀ (a b : ℝ)
        (E : ZetaAdmissibleFunction.CompletedZetaZeroExcisedStrip a b)
        (N : ℕ) (z : ℂ),
        z ∈ E.carrier →
          ∀ w : ℂ,
            w ∈ Metric.sphere z (zetaRadius a b E N) →
              ‖ZetaAdmissibleFunction.zetaSideFactor w‖ ≤
                zetaAmplitude a b E N * (1 + ‖z.im‖) ^ N)
    (zetaValueLower_bound :
      ∀ (a b : ℝ)
        (E : ZetaAdmissibleFunction.CompletedZetaZeroExcisedStrip a b)
        (N : ℕ) (z : ℂ),
        z ∈ E.carrier →
          zetaValueLower a b E N ≤
            ‖ZetaAdmissibleFunction.zetaSideFactor z‖)
    (gammaDiffCont :
      ∀ (a b : ℝ)
        (E : ZetaAdmissibleFunction.CompletedZetaZeroExcisedStrip a b)
        (N : ℕ) (z : ℂ),
        z ∈ E.carrier →
          DiffContOnCl ℂ
            (fun w : ℂ => (Complex.Gammaℝ w)⁻¹)
            (Metric.ball z (gammaRadius a b E N)))
    (gammaSphereBound :
      ∀ (a b : ℝ)
        (E : ZetaAdmissibleFunction.CompletedZetaZeroExcisedStrip a b)
        (N : ℕ) (z : ℂ),
        z ∈ E.carrier →
          ∀ w : ℂ,
            w ∈ Metric.sphere z (gammaRadius a b E N) →
              ‖(Complex.Gammaℝ w)⁻¹‖ ≤
                gammaAmplitude a b E N * (1 + ‖z.im‖) ^ N)
    (gammaValueLower_bound :
      ∀ (a b : ℝ)
        (E : ZetaAdmissibleFunction.CompletedZetaZeroExcisedStrip a b)
        (N : ℕ) (z : ℂ),
        z ∈ E.carrier →
          gammaValueLower a b E N ≤ ‖(Complex.Gammaℝ z)⁻¹‖) :
    ZetaWeilQuadraticPositivity :=
  zetaWeilQuadraticPositivity_of_globalFactorBoundData_final_owner
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

/-- Canonical scheduled-carrier Cauchy factor estimates and concrete
autocorrelation completed-log-derivative control construct the corrected
pole-corrected common limit. -/
theorem zetaCompletedAutocorrelationPoleCorrectedCommonLimit_of_canonicalCarrierCauchyFactorData_concreteControl_final_owner
    (separated :
      ∀ f : ZetaAdmissibleFunction,
        (ZetaAdmissibleFunction.zetaCompletedExplicitFormulaAutocorrelationScheduledHorizontalCarrier
          f).HasPositiveSingularSeparation)
    (zetaRadius zetaAmplitude zetaValueLower :
      ∀ f : ZetaAdmissibleFunction, ℕ → ℝ)
    (gammaRadius gammaAmplitude gammaValueLower :
      ∀ f : ZetaAdmissibleFunction, ℕ → ℝ)
    (zetaRadius_pos :
      ∀ (f : ZetaAdmissibleFunction) (N : ℕ),
        0 < zetaRadius f N)
    (zetaAmplitude_pos :
      ∀ (f : ZetaAdmissibleFunction) (N : ℕ),
        0 < zetaAmplitude f N)
    (zetaValueLower_pos :
      ∀ (f : ZetaAdmissibleFunction) (N : ℕ),
        0 < zetaValueLower f N)
    (gammaRadius_pos :
      ∀ (f : ZetaAdmissibleFunction) (N : ℕ),
        0 < gammaRadius f N)
    (gammaAmplitude_pos :
      ∀ (f : ZetaAdmissibleFunction) (N : ℕ),
        0 < gammaAmplitude f N)
    (gammaValueLower_pos :
      ∀ (f : ZetaAdmissibleFunction) (N : ℕ),
        0 < gammaValueLower f N)
    (zetaDiffCont :
      ∀ (f : ZetaAdmissibleFunction) (N : ℕ) (z : ℂ),
        z ∈
          (ZetaAdmissibleFunction.zetaCompletedExplicitFormulaAutocorrelationScheduledHorizontalCarrier
            f).carrier →
        DiffContOnCl ℂ ZetaAdmissibleFunction.zetaSideFactor
          (Metric.ball z (zetaRadius f N)))
    (zetaSphereBound :
      ∀ (f : ZetaAdmissibleFunction) (N : ℕ) (z : ℂ),
        z ∈
          (ZetaAdmissibleFunction.zetaCompletedExplicitFormulaAutocorrelationScheduledHorizontalCarrier
            f).carrier →
        ∀ w : ℂ,
          w ∈ Metric.sphere z (zetaRadius f N) →
          ‖ZetaAdmissibleFunction.zetaSideFactor w‖ ≤
            zetaAmplitude f N * (1 + ‖z.im‖) ^ N)
    (zetaValueLower_bound :
      ∀ (f : ZetaAdmissibleFunction) (N : ℕ) (z : ℂ),
        z ∈
          (ZetaAdmissibleFunction.zetaCompletedExplicitFormulaAutocorrelationScheduledHorizontalCarrier
            f).carrier →
        zetaValueLower f N ≤ ‖ZetaAdmissibleFunction.zetaSideFactor z‖)
    (gammaDiffCont :
      ∀ (f : ZetaAdmissibleFunction) (N : ℕ) (z : ℂ),
        z ∈
          (ZetaAdmissibleFunction.zetaCompletedExplicitFormulaAutocorrelationScheduledHorizontalCarrier
            f).carrier →
        DiffContOnCl ℂ
          (fun w : ℂ => (Complex.Gammaℝ w)⁻¹)
          (Metric.ball z (gammaRadius f N)))
    (gammaSphereBound :
      ∀ (f : ZetaAdmissibleFunction) (N : ℕ) (z : ℂ),
        z ∈
          (ZetaAdmissibleFunction.zetaCompletedExplicitFormulaAutocorrelationScheduledHorizontalCarrier
            f).carrier →
        ∀ w : ℂ,
          w ∈ Metric.sphere z (gammaRadius f N) →
          ‖(Complex.Gammaℝ w)⁻¹‖ ≤
            gammaAmplitude f N * (1 + ‖z.im‖) ^ N)
    (gammaValueLower_bound :
      ∀ (f : ZetaAdmissibleFunction) (N : ℕ) (z : ℂ),
        z ∈
          (ZetaAdmissibleFunction.zetaCompletedExplicitFormulaAutocorrelationScheduledHorizontalCarrier
            f).carrier →
        gammaValueLower f N ≤ ‖(Complex.Gammaℝ z)⁻¹‖)
    (hConcrete :
      ZetaAdmissibleFunction.CompletedZetaNegLogDerivAutocorrelationConcreteControl) :
    ZetaCompletedAutocorrelationPoleCorrectedCommonLimit :=
  zetaCompletedAutocorrelationPoleCorrectedCommonLimit_of_canonicalScheduledCarrierFactorData_concreteControl_final_owner
    (ZetaAdmissibleFunction.zetaCompletedExplicitFormulaAutocorrelationScheduledHorizontalCarrier_factorData_of_cauchyLogDerivative_owner
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
    hConcrete

end

end LFunctions
end Boundary
