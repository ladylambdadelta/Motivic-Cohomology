import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaCompletedLogDerivativeControl.FactorBoundData
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaCompletedLogDerivativeControl.CauchyBoundData
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaZeroKreinGram.WeilCriterion.OwnerParts.CanonicalScheduledPolynomialPackageParts.CarrierFactorData

/-!
# Canonical carrier Cauchy factor data

This file owns the narrow constructor for factor-bound data on the canonical
scheduled horizontal carriers used in the RH lane.
-/

namespace Boundary
namespace LFunctions

noncomputable section

namespace ZetaAdmissibleFunction

theorem zetaSideFactor_cauchy_log_derivative_bound_of_singular_separation
    (z : ℂ) (R δ : ℝ)
    (hseparated : ∀ q : ℂ,
      explicitFormulaContourSingularPoint q → δ ≤ ‖z - q‖)
    (hR : R < δ) (hR_pos : 0 < R) :
    ∃ B : ℝ, 0 < B ∧
      ‖deriv zetaSideFactor z / zetaSideFactor z‖ ≤ B := by
  apply zetaSideFactor_cauchy_log_derivative_bound_of_closedBall_nonzero
    R hR_pos
    (zetaSideFactor_diffContOnCl_of_singular_separation z R δ hseparated hR)
  exact zetaSideFactor_ne_zero_on_closedBall_of_singular_separation
    z R δ hseparated hR

theorem inverseGamma_cauchy_log_derivative_bound_of_singular_separation
    (z : ℂ) (R δ : ℝ)
    (hseparated : ∀ q : ℂ,
      explicitFormulaContourSingularPoint q → δ ≤ ‖z - q‖)
    (hR : R < δ) (hR_pos : 0 < R) :
    ∃ B : ℝ, 0 < B ∧
      ‖deriv (fun w : ℂ => (Complex.Gammaℝ w)⁻¹) z /
          (Complex.Gammaℝ z)⁻¹‖ ≤ B := by
  apply inverseGamma_cauchy_log_derivative_bound_of_closedBall_nonzero
    R hR_pos
    (Differentiable.diffContOnCl Complex.differentiable_Gammaℝ_inv)
  exact inverseGamma_ne_zero_on_closedBall_of_singular_separation
    z R δ hseparated hR

/-- Cauchy estimates on each canonical scheduled horizontal carrier produce the
canonical carrier factor-bound data consumed in the positivity owner chain. -/
def zetaCompletedExplicitFormulaAutocorrelationScheduledHorizontalCarrier_factorData_of_cauchyLogDerivative_owner
    (separated :
      ∀ f : ZetaAdmissibleFunction,
        (zetaCompletedExplicitFormulaAutocorrelationScheduledHorizontalCarrier f)
          .HasPositiveSingularSeparation)
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
          (zetaCompletedExplicitFormulaAutocorrelationScheduledHorizontalCarrier
            f).carrier →
        DiffContOnCl ℂ zetaSideFactor (Metric.ball z (zetaRadius f N)))
    (zetaSphereBound :
      ∀ (f : ZetaAdmissibleFunction) (N : ℕ) (z : ℂ),
        z ∈
          (zetaCompletedExplicitFormulaAutocorrelationScheduledHorizontalCarrier
            f).carrier →
        ∀ w : ℂ,
          w ∈ Metric.sphere z (zetaRadius f N) →
          ‖zetaSideFactor w‖ ≤ zetaAmplitude f N * (1 + ‖z.im‖) ^ N)
    (zetaValueLower_bound :
      ∀ (f : ZetaAdmissibleFunction) (N : ℕ) (z : ℂ),
        z ∈
          (zetaCompletedExplicitFormulaAutocorrelationScheduledHorizontalCarrier
            f).carrier →
        zetaValueLower f N ≤ ‖zetaSideFactor z‖)
    (gammaDiffCont :
      ∀ (f : ZetaAdmissibleFunction) (N : ℕ) (z : ℂ),
        z ∈
          (zetaCompletedExplicitFormulaAutocorrelationScheduledHorizontalCarrier
            f).carrier →
        DiffContOnCl ℂ
          (fun w : ℂ => (Complex.Gammaℝ w)⁻¹)
          (Metric.ball z (gammaRadius f N)))
    (gammaSphereBound :
      ∀ (f : ZetaAdmissibleFunction) (N : ℕ) (z : ℂ),
        z ∈
          (zetaCompletedExplicitFormulaAutocorrelationScheduledHorizontalCarrier
            f).carrier →
        ∀ w : ℂ,
          w ∈ Metric.sphere z (gammaRadius f N) →
          ‖(Complex.Gammaℝ w)⁻¹‖ ≤
            gammaAmplitude f N * (1 + ‖z.im‖) ^ N)
    (gammaValueLower_bound :
      ∀ (f : ZetaAdmissibleFunction) (N : ℕ) (z : ℂ),
        z ∈
          (zetaCompletedExplicitFormulaAutocorrelationScheduledHorizontalCarrier
            f).carrier →
        gammaValueLower f N ≤ ‖(Complex.Gammaℝ z)⁻¹‖) :
    ∀ f : ZetaAdmissibleFunction,
      CompletedZetaZeroExcisedStrip.FactorBoundData
        (zetaCompletedExplicitFormulaAutocorrelationScheduledHorizontalCarrier f) :=
  fun f =>
    CompletedZetaZeroExcisedStrip.FactorBoundData.ofCauchyLogDerivative
      (zetaCompletedExplicitFormulaAutocorrelationScheduledHorizontalCarrier f)
      (separated f)
      (zetaRadius f)
      (zetaAmplitude f)
      (zetaValueLower f)
      (gammaRadius f)
      (gammaAmplitude f)
      (gammaValueLower f)
      (zetaRadius_pos f)
      (zetaAmplitude_pos f)
      (zetaValueLower_pos f)
      (gammaRadius_pos f)
      (gammaAmplitude_pos f)
      (gammaValueLower_pos f)
      (zetaDiffCont f)
      (zetaSphereBound f)
      (zetaValueLower_bound f)
      (gammaDiffCont f)
      (gammaSphereBound f)
      (gammaValueLower_bound f)

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
