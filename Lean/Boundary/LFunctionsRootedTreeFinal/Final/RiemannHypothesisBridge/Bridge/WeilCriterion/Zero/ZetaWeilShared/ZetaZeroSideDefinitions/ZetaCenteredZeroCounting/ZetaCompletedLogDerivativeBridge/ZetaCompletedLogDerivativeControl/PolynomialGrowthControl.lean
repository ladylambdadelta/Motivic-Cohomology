import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaCompletedLogDerivativeControl.FactorBoundData

/-!
# Fixed-degree completed-log-derivative growth control

This file owns the polynomial-growth surface actually supplied by logarithmic
derivative estimates: one sufficient degree on each zero-excised carrier.
-/

namespace Boundary
namespace LFunctions

noncomputable section

namespace ZetaAdmissibleFunction

structure CompletedZetaNegLogDerivPolynomialGrowthControl
    (f : ZetaAdmissibleFunction) where
  zero_excised_polynomial_growth :
    ∀ (a b : ℝ) (E : CompletedZetaZeroExcisedStrip a b),
      ∃ K : ℕ,
        ∃ C : ℝ,
          0 < C ∧
          ∀ z : ℂ,
            z ∈ E.carrier →
            ‖completedZetaNegLogDeriv z‖ ≤ C * (1 + ‖z.im‖) ^ K

def CompletedZetaNegLogDerivPolynomialGrowthControl.ofFullControl
    {f : ZetaAdmissibleFunction}
    (h : CompletedZetaNegLogDerivControl f) :
    CompletedZetaNegLogDerivPolynomialGrowthControl f :=
  { zero_excised_polynomial_growth :=
      fun a b E => h.zero_excised_polynomial_growth a b E }

structure CompletedZetaNegLogDerivCommonDegreeFactorControl where
  K : ∀ (a b : ℝ), CompletedZetaZeroExcisedStrip a b → ℕ
  Czeta : ∀ (a b : ℝ), CompletedZetaZeroExcisedStrip a b → ℝ
  Cgamma : ∀ (a b : ℝ), CompletedZetaZeroExcisedStrip a b → ℝ
  Czeta_pos :
    ∀ (a b : ℝ) (E : CompletedZetaZeroExcisedStrip a b),
      0 < Czeta a b E
  Cgamma_pos :
    ∀ (a b : ℝ) (E : CompletedZetaZeroExcisedStrip a b),
      0 < Cgamma a b E
  Czeta_bound :
    ∀ (a b : ℝ) (E : CompletedZetaZeroExcisedStrip a b) (z : ℂ),
      z ∈ E.carrier →
      ‖zetaSideNegLogDeriv z‖ ≤
        Czeta a b E * (1 + ‖z.im‖) ^ K a b E
  Cgamma_bound :
    ∀ (a b : ℝ) (E : CompletedZetaZeroExcisedStrip a b) (z : ℂ),
      z ∈ E.carrier →
      ‖deriv (fun w : ℂ => (Complex.Gammaℝ w)⁻¹) z /
          (Complex.Gammaℝ z)⁻¹‖ ≤
        Cgamma a b E * (1 + ‖z.im‖) ^ K a b E

theorem completedZetaNegLogDeriv_polynomial_bound_of_common_degree_factor_control_owner
    (h : CompletedZetaNegLogDerivCommonDegreeFactorControl)
    (a b : ℝ) (E : CompletedZetaZeroExcisedStrip a b) :
    ∃ K : ℕ, ∃ C : ℝ,
      0 < C ∧
      ∀ z : ℂ, z ∈ E.carrier →
        ‖completedZetaNegLogDeriv z‖ ≤ C * (1 + ‖z.im‖) ^ K := by
  refine ⟨h.K a b E, h.Czeta a b E + h.Cgamma a b E, ?_, ?_⟩
  · exact add_pos (h.Czeta_pos a b E) (h.Cgamma_pos a b E)
  · intro z hz
    exact completedZetaNegLogDeriv_norm_bound_of_factor_bounds
      E (h.K a b E) (h.Czeta a b E) (h.Cgamma a b E) z hz
      (h.Czeta_bound a b E)
      (h.Cgamma_bound a b E)

def CompletedZetaNegLogDerivPolynomialGrowthControl.ofCommonDegreeFactorControl
    (f : ZetaAdmissibleFunction)
    (h : CompletedZetaNegLogDerivCommonDegreeFactorControl) :
    CompletedZetaNegLogDerivPolynomialGrowthControl f :=
  { zero_excised_polynomial_growth :=
      fun a b E =>
        completedZetaNegLogDeriv_polynomial_bound_of_common_degree_factor_control_owner
          h a b E }

def completedZetaNegLogDeriv_common_degree_factor_control_of_factor_bound_data_owner
    (data :
      ∀ (a b : ℝ) (E : CompletedZetaZeroExcisedStrip a b),
        CompletedZetaZeroExcisedStrip.FactorBoundData E) :
    CompletedZetaNegLogDerivCommonDegreeFactorControl :=
  { K := fun _a _b _E => 0
    Czeta := fun a b E => (data a b E).zetaSide.constant 0
    Cgamma := fun a b E => (data a b E).inverseGamma.constant 0
    Czeta_pos := fun a b E => (data a b E).zetaSide.constant_pos 0
    Cgamma_pos := fun a b E => (data a b E).inverseGamma.constant_pos 0
    Czeta_bound :=
      fun a b E z hz => (data a b E).zetaSide.bound 0 z hz
    Cgamma_bound :=
      fun a b E z hz => (data a b E).inverseGamma.bound 0 z hz }

def CompletedZetaNegLogDerivCommonDegreeFactorControl.ofFactorBoundData
    (data :
      ∀ (a b : ℝ) (E : CompletedZetaZeroExcisedStrip a b),
        CompletedZetaZeroExcisedStrip.FactorBoundData E) :
    CompletedZetaNegLogDerivCommonDegreeFactorControl :=
  completedZetaNegLogDeriv_common_degree_factor_control_of_factor_bound_data_owner
    data

structure CompletedZetaNegLogDerivAutocorrelationCommonDegreeFactorControl where
  K :
    ∀ (f : ZetaAdmissibleFunction) (a b : ℝ),
      CompletedZetaZeroExcisedStrip a b → ℕ
  Czeta :
    ∀ (f : ZetaAdmissibleFunction) (a b : ℝ),
      CompletedZetaZeroExcisedStrip a b → ℝ
  Cgamma :
    ∀ (f : ZetaAdmissibleFunction) (a b : ℝ),
      CompletedZetaZeroExcisedStrip a b → ℝ
  Czeta_pos :
    ∀ (f : ZetaAdmissibleFunction) (a b : ℝ)
      (E : CompletedZetaZeroExcisedStrip a b),
      0 < Czeta f a b E
  Cgamma_pos :
    ∀ (f : ZetaAdmissibleFunction) (a b : ℝ)
      (E : CompletedZetaZeroExcisedStrip a b),
      0 < Cgamma f a b E
  Czeta_bound :
    ∀ (f : ZetaAdmissibleFunction) (a b : ℝ)
      (E : CompletedZetaZeroExcisedStrip a b) (z : ℂ),
      z ∈ E.carrier →
      ‖zetaSideNegLogDeriv z‖ ≤
        Czeta f a b E * (1 + ‖z.im‖) ^ K f a b E
  Cgamma_bound :
    ∀ (f : ZetaAdmissibleFunction) (a b : ℝ)
      (E : CompletedZetaZeroExcisedStrip a b) (z : ℂ),
      z ∈ E.carrier →
      ‖deriv (fun w : ℂ => (Complex.Gammaℝ w)⁻¹) z /
          (Complex.Gammaℝ z)⁻¹‖ ≤
        Cgamma f a b E * (1 + ‖z.im‖) ^ K f a b E

def CompletedZetaNegLogDerivAutocorrelationCommonDegreeFactorControl.atSeed
    (h : CompletedZetaNegLogDerivAutocorrelationCommonDegreeFactorControl)
    (f : ZetaAdmissibleFunction) :
    CompletedZetaNegLogDerivCommonDegreeFactorControl :=
  { K := h.K f
    Czeta := h.Czeta f
    Cgamma := h.Cgamma f
    Czeta_pos := h.Czeta_pos f
    Cgamma_pos := h.Cgamma_pos f
    Czeta_bound := h.Czeta_bound f
    Cgamma_bound := h.Cgamma_bound f }

def completedZetaNegLogDerivPolynomialGrowthControl_autocorrelation_of_commonDegreeFactorControl
    (h : CompletedZetaNegLogDerivAutocorrelationCommonDegreeFactorControl) :
    ∀ f : ZetaAdmissibleFunction,
      CompletedZetaNegLogDerivPolynomialGrowthControl
        (ZetaAdmissibleFunction.convolutionAutocorrelation f) :=
  fun f =>
    CompletedZetaNegLogDerivPolynomialGrowthControl.ofCommonDegreeFactorControl
      (ZetaAdmissibleFunction.convolutionAutocorrelation f)
      (h.atSeed f)

def completedZetaNegLogDerivAutocorrelationCommonDegreeFactorControl_of_concreteControl
    (h : CompletedZetaNegLogDerivAutocorrelationConcreteControl) :
    CompletedZetaNegLogDerivAutocorrelationCommonDegreeFactorControl :=
  { K := fun seed stripLeft stripRight carrier => 0
    Czeta := fun f a b E => h.zetaSide.Czeta f a b E 0
    Cgamma := fun f a b E => h.inverseGamma.Cgamma f a b E 0
    Czeta_pos := fun f a b E => h.zetaSide.Czeta_pos f a b E 0
    Cgamma_pos := fun f a b E => h.inverseGamma.Cgamma_pos f a b E 0
    Czeta_bound := fun f a b E z hz => h.zetaSide.Czeta_bound f a b E 0 z hz
    Cgamma_bound := fun f a b E z hz => h.inverseGamma.Cgamma_bound f a b E 0 z hz }

def completedZetaNegLogDerivAutocorrelationCommonDegreeFactorControl_of_factorBoundData_owner
    (data :
      ∀ (a b : ℝ) (E : CompletedZetaZeroExcisedStrip a b),
        CompletedZetaZeroExcisedStrip.FactorBoundData E) :
    CompletedZetaNegLogDerivAutocorrelationCommonDegreeFactorControl :=
  { K := fun _f _a _b _E => 0
    Czeta := fun _f a b E => (data a b E).zetaSide.constant 0
    Cgamma := fun _f a b E => (data a b E).inverseGamma.constant 0
    Czeta_pos := fun _f a b E => (data a b E).zetaSide.constant_pos 0
    Cgamma_pos := fun _f a b E => (data a b E).inverseGamma.constant_pos 0
    Czeta_bound :=
      fun _f a b E z hz => (data a b E).zetaSide.bound 0 z hz
    Cgamma_bound :=
      fun _f a b E z hz => (data a b E).inverseGamma.bound 0 z hz }

def completedZetaNegLogDerivPolynomialGrowthControl_autocorrelation_of_factorBoundData_owner
    (data :
      ∀ (a b : ℝ) (E : CompletedZetaZeroExcisedStrip a b),
        CompletedZetaZeroExcisedStrip.FactorBoundData E) :
    ∀ f : ZetaAdmissibleFunction,
      CompletedZetaNegLogDerivPolynomialGrowthControl
        (ZetaAdmissibleFunction.convolutionAutocorrelation f) :=
  completedZetaNegLogDerivPolynomialGrowthControl_autocorrelation_of_commonDegreeFactorControl
    (completedZetaNegLogDerivAutocorrelationCommonDegreeFactorControl_of_factorBoundData_owner
      data)

def completedZetaNegLogDerivPolynomialGrowthControl_autocorrelation_of_fullControl
    (hLog :
      ∀ f : ZetaAdmissibleFunction,
        CompletedZetaNegLogDerivControl
          (ZetaAdmissibleFunction.convolutionAutocorrelation f)) :
    ∀ f : ZetaAdmissibleFunction,
      CompletedZetaNegLogDerivPolynomialGrowthControl
        (ZetaAdmissibleFunction.convolutionAutocorrelation f) :=
  fun f =>
    CompletedZetaNegLogDerivPolynomialGrowthControl.ofFullControl (hLog f)

def completedZetaNegLogDerivPolynomialGrowthControl_autocorrelation_of_concreteControl_owner
    (hLogConcrete :
      CompletedZetaNegLogDerivAutocorrelationConcreteControl) :
    ∀ f : ZetaAdmissibleFunction,
      CompletedZetaNegLogDerivPolynomialGrowthControl
        (ZetaAdmissibleFunction.convolutionAutocorrelation f) :=
  completedZetaNegLogDerivPolynomialGrowthControl_autocorrelation_of_commonDegreeFactorControl
    (completedZetaNegLogDerivAutocorrelationCommonDegreeFactorControl_of_concreteControl
      hLogConcrete)

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
