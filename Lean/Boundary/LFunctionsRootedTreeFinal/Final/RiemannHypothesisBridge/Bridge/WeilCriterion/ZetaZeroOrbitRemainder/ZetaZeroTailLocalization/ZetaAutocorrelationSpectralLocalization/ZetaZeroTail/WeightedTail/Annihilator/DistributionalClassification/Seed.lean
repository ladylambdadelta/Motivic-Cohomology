import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaZeroTail.WeightedTail.Annihilator.DistributionalClassification.TranslationMoments
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaTransformCalculus.Owner

/-!
# Nonzero seeds for completed-zero coefficients

Every completed-zero coordinate admits an admissible probe with nonzero
zero-side value.  Consequently a nonzero bounded coefficient has a nonzero
multiplicity-weighted seeded translation coefficient.
-/

namespace Boundary
namespace LFunctions
noncomputable section
namespace ZetaAdmissibleFunction

theorem exists_zetaZeroSideContribution_nonzero_probe
    (rho : ZetaCompletedZeroCoordinate) :
    ∃ f : ZetaAdmissibleFunction,
      zetaZeroSideContribution (rho : ℂ) f ≠ 0 := by
  obtain ⟨f, hf⟩ := exists_zetaLaplaceTransform_nonzero_seed (rho : ℂ)
  exact
    ⟨f, fun hside =>
      hf
        ((zetaSpectralEval_eq_laplace f (rho : ℂ)).symm.trans
          (zetaSpectralEval_eq_zero_of_zetaZeroSideContribution_eq_zero
            rho f hside))⟩

theorem exists_nonzero_completedZeroTranslationSeededCoefficient
    (b : lp (fun rhoCoordinate : ZetaCompletedZeroCoordinate => ℂ) (∞ : ENNReal))
    (rho : ZetaCompletedZeroCoordinate)
    (hrho : b rho ≠ 0) :
    ∃ f : ZetaAdmissibleFunction,
      completedZeroTranslationSeededCoefficient b f rho ≠ 0 := by
  obtain ⟨f, hside⟩ := exists_zetaZeroSideContribution_nonzero_probe rho
  have hproduct :
      b rho * zetaZeroSideContribution (rho : ℂ) f ≠ 0 :=
    mul_ne_zero hrho hside
  exact ⟨f, hproduct⟩

end ZetaAdmissibleFunction
end
end LFunctions
end Boundary
