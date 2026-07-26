import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaZeroKreinGram.WeilCriterion.OwnerParts.CanonicalCarrierCauchyFactorData
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaZeroKreinGram.WeilCriterion.OwnerParts.CauchyPathPositivity

/-!
# Canonical carrier Cauchy factor positivity

This file connects canonical scheduled-carrier Cauchy factor estimates to the
raw Weil positivity theorem.
-/

namespace Boundary
namespace LFunctions

noncomputable section

/-- Raw Weil positivity from canonical scheduled-carrier Cauchy factor estimates
and physical completed-log-derivative control. -/
theorem zetaWeilQuadraticPositivity_of_canonicalCarrierCauchyFactorData_physicalLogDerivControl_owner
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
    (hLog :
      ∀ f : ZetaAdmissibleFunction,
        ZetaAdmissibleFunction.CompletedZetaNegLogDerivControl
          (zetaAutocorrelationPhysicalProbe f)) :
    ZetaWeilQuadraticPositivity :=
  zetaWeilQuadraticPositivity_of_canonicalScheduledCarrierFactorData_physicalLogDerivControl_owner
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
    hLog

end

end LFunctions
end Boundary
