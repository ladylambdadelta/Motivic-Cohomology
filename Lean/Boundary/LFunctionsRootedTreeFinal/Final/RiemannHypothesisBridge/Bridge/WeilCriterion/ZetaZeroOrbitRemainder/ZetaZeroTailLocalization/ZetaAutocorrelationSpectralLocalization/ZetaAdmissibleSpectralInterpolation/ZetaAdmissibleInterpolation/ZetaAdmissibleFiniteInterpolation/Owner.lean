import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaAdmissibleSpectralInterpolation.ZetaAdmissibleInterpolation.ZetaAdmissibleFiniteInterpolation.ZetaAdmissibleBump.Owner

/-!
# Boundary admissible finite interpolation

This file packages the finite interpolation output of the admissible bump
library into a finite-sample form that is easier to consume later on the
spectral/separation side.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped CompactlySupported

namespace ZetaAdmissibleFunction

/-- A finite sample admits an admissible interpolant with compact support. -/
theorem exists_admissible_eval_sample_with_support (S : ZetaAdmissibleFunction.FiniteSample)
    (a : Fin S.n → ℂ) :
    ∃ f : ZetaAdmissibleFunction, (∀ i, f (S.x i) = a i) ∧ HasCompactSupport f := by
  exact
    match exists_admissible_delta_sample_with_support S with
    | ⟨F, hF1, hF0, hFc⟩ =>
        Exists.intro (sampleInterpolant S a F)
          (And.intro
            (fun i => sampleInterpolant_apply S a F hF1 hF0 i)
            (sampleInterpolant_hasCompactSupport S a F))

/-- A finite sample admits a compactly supported interpolant whose support is controlled by the
support of the chosen delta basis. -/
theorem exists_admissible_eval_sample_with_basis_support (S : ZetaAdmissibleFunction.FiniteSample)
    (a : Fin S.n → ℂ) :
    ∃ F : ∀ _i, ZetaAdmissibleFunction,
      (∀ i, F i (S.x i) = (1 : ℂ)) ∧
      (∀ i j, j ≠ i → F i (S.x j) = 0) ∧
      (∀ i, HasCompactSupport (F i)) ∧
      ∃ f : ZetaAdmissibleFunction,
        (∀ i, f (S.x i) = a i) ∧
        HasCompactSupport f ∧
        Function.support f ⊆ Set.iUnion fun i => Function.support (F i) := by
  exact
    match exists_admissible_delta_sample_with_support S with
    | ⟨F, hF1, hF0, hFc⟩ =>
        Exists.intro F
          (And.intro hF1
            (And.intro hF0
              (And.intro hFc
                (Exists.intro (sampleInterpolant S a F)
                  (And.intro
                    (fun i => sampleInterpolant_apply S a F hF1 hF0 i)
                    (And.intro
                      (sampleInterpolant_hasCompactSupport S a F)
                      (sampleInterpolant_support_subset_iUnion S a F)))))))

/-- A finite sample admits a compactly supported interpolant together with a delta basis whose
supports are individually contained in closed balls. -/
theorem exists_admissible_eval_sample_with_basis_closedBall_support
    (S : ZetaAdmissibleFunction.FiniteSample) (a : Fin S.n → ℂ) :
    ∃ F : ∀ _i, ZetaAdmissibleFunction,
      (∀ i, F i (S.x i) = (1 : ℂ)) ∧
      (∀ i j, j ≠ i → F i (S.x j) = 0) ∧
      (∀ i, ∃ rOut : ℝ, 0 < rOut ∧ Function.support (F i) ⊆ Metric.closedBall (S.x i) rOut) ∧
      ∃ f : ZetaAdmissibleFunction,
        (∀ i, f (S.x i) = a i) ∧
        HasCompactSupport f ∧
        Function.support f ⊆ Set.iUnion fun i => Function.support (F i) := by
  exact
    match exists_admissible_delta_sample_with_closedBall_support S with
    | ⟨F, hF1, hF0, hFr⟩ =>
        Exists.intro F
          (And.intro hF1
            (And.intro hF0
              (And.intro hFr
                (Exists.intro (sampleInterpolant S a F)
                  (And.intro
                    (fun i => sampleInterpolant_apply S a F hF1 hF0 i)
                    (And.intro
                      (sampleInterpolant_hasCompactSupport S a F)
                      (sampleInterpolant_support_subset_iUnion S a F)))))))

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
