import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaCompletedLogDerivativeControl.FactorBoundData

/-!
# Global Cauchy factor-bound data

This file owns the global constructor from separated-carrier Cauchy estimates
to concrete completed-log-derivative factor-bound data.
-/

namespace Boundary
namespace LFunctions

noncomputable section

namespace ZetaAdmissibleFunction

/-- Global factor-bound data from Cauchy estimates on every separated
zero-excised strip carrier. -/
def CompletedZetaZeroExcisedStrip.factorBoundData_of_globalCauchyLogDerivative_owner
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
    ∀ (a b : ℝ) (E : CompletedZetaZeroExcisedStrip a b),
      CompletedZetaZeroExcisedStrip.FactorBoundData E :=
  fun a b E =>
    CompletedZetaZeroExcisedStrip.FactorBoundData.ofCauchyLogDerivative
      E
      (separated a b E)
      (zetaRadius a b E)
      (zetaAmplitude a b E)
      (zetaValueLower a b E)
      (gammaRadius a b E)
      (gammaAmplitude a b E)
      (gammaValueLower a b E)
      (zetaRadius_pos a b E)
      (zetaAmplitude_pos a b E)
      (zetaValueLower_pos a b E)
      (gammaRadius_pos a b E)
      (gammaAmplitude_pos a b E)
      (gammaValueLower_pos a b E)
      (zetaDiffCont a b E)
      (zetaSphereBound a b E)
      (zetaValueLower_bound a b E)
      (gammaDiffCont a b E)
      (gammaSphereBound a b E)
      (gammaValueLower_bound a b E)

/-- Global factor data assembled directly from the two concrete
logarithmic-derivative owner packages. -/
def CompletedZetaZeroExcisedStrip.factorBoundData_of_globalLogDeriv_owner
    (zetaData :
      ∀ (a b : ℝ) (E : CompletedZetaZeroExcisedStrip a b),
        CompletedZetaZeroExcisedStrip.ZetaSideBoundData E)
    (gammaData :
      ∀ (a b : ℝ) (E : CompletedZetaZeroExcisedStrip a b),
        CompletedZetaZeroExcisedStrip.InverseGammaBoundData E) :
    ∀ (a b : ℝ) (E : CompletedZetaZeroExcisedStrip a b),
      CompletedZetaZeroExcisedStrip.FactorBoundData E :=
  fun a b E =>
    CompletedZetaZeroExcisedStrip.FactorBoundData.ofLogDerivBounds
      (zetaData a b E)
      (gammaData a b E)

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
