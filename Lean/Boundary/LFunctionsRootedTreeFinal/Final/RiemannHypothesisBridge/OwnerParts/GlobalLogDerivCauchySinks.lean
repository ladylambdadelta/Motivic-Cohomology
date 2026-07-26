import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.OwnerParts.BoundaryTraceBesselPacket
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaCompletedLogDerivativeControl.GlobalCauchyFactorData

/-!
# Global log-derivative Cauchy sinks

This file owns the final RH bridge from explicit zero-excised Cauchy
log-derivative estimates to the global factor-bound-data sink consumed by the
Trace-Bessel packet route.
-/

namespace Boundary
namespace LFunctions

noncomputable section

/-- Canonical scheduled-carrier separation and split global logarithmic
derivative polynomial constants give the Boundary RH statement. -/
theorem boundaryRiemannHypothesis_of_canonicalCarrierGlobalSplitLogDerivConstants_owner
    (separated :
      ∀ f : ZetaAdmissibleFunction,
        (ZetaAdmissibleFunction.zetaCompletedExplicitFormulaAutocorrelationScheduledHorizontalCarrier
          f).HasPositiveSingularSeparation)
    (Czeta Cgamma :
      ∀ (f : ZetaAdmissibleFunction) (a b : ℝ),
        ZetaAdmissibleFunction.CompletedZetaZeroExcisedStrip a b → ℕ → ℝ)
    (Czeta_pos :
      ∀ (f : ZetaAdmissibleFunction) (a b : ℝ)
        (E : ZetaAdmissibleFunction.CompletedZetaZeroExcisedStrip a b)
        (N : ℕ),
        0 < Czeta f a b E N)
    (Cgamma_pos :
      ∀ (f : ZetaAdmissibleFunction) (a b : ℝ)
        (E : ZetaAdmissibleFunction.CompletedZetaZeroExcisedStrip a b)
        (N : ℕ),
        0 < Cgamma f a b E N)
    (Czeta_bound :
      ∀ (f : ZetaAdmissibleFunction) (a b : ℝ)
        (E : ZetaAdmissibleFunction.CompletedZetaZeroExcisedStrip a b)
        (N : ℕ) (z : ℂ),
        z ∈ E.carrier →
        ‖ZetaAdmissibleFunction.zetaSideNegLogDeriv z‖ ≤
          Czeta f a b E N * (1 + ‖z.im‖) ^ N)
    (Cgamma_bound :
      ∀ (f : ZetaAdmissibleFunction) (a b : ℝ)
        (E : ZetaAdmissibleFunction.CompletedZetaZeroExcisedStrip a b)
        (N : ℕ) (z : ℂ),
        z ∈ E.carrier →
        ‖deriv (fun w : ℂ => (Complex.Gammaℝ w)⁻¹) z /
            (Complex.Gammaℝ z)⁻¹‖ ≤
          Cgamma f a b E N * (1 + ‖z.im‖) ^ N) :
    boundaryRiemannHypothesis :=
  boundaryRiemannHypothesis_of_globalSplitLogDerivConstants_packet_owner
    separated
    Czeta
    Cgamma
    Czeta_pos
    Cgamma_pos
    Czeta_bound
    Cgamma_bound

/-- Global zero-excised Cauchy log-derivative estimates give the Boundary RH
statement through the global factor-bound-data sink. -/
theorem boundaryRiemannHypothesis_of_globalCauchyLogDerivativeData_owner
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
    boundaryRiemannHypothesis :=
  boundaryRiemannHypothesis_of_canonicalTransform_logDerivFactorBoundData_packet_owner
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

end
end LFunctions
end Boundary
