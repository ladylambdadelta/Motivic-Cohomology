import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaZeroTail.WeightedTail.Annihilator.Owner

/-!
# Completed-zero annihilator vanishing predicate

This file owns the probewise vanishing predicate used by finite-window
coefficient uniqueness and by distributional classification.
-/

namespace Boundary
namespace LFunctions
noncomputable section
namespace ZetaAdmissibleFunction

open scoped ENNReal

/-- A bounded completed-zero coefficient family annihilates the admissible
probe space. -/
def ZetaCompletedZeroSideAnnihilatorVanishes
    (b : lp (fun coordinate : ZetaCompletedZeroCoordinate => ℂ) (∞ : ENNReal))
    (hbranch : Complex.BinetSecondFormulaBranchUniformTailAbsorption)
    (hpartialOneTwo : BoundaryLineOneAbelPartialMajorant)
    (hcompactOneTwo : PoleClearedOneTwoStripCompactBoundaryBound)
    (hfinite : PoleClearedRightCriticalStripAdmissibleGrowth)
    (hpartialLeft : ReflectedBoundaryAbelPartialMajorant)
    (hcompactBoundary : PoleClearedRightCriticalStripCompactBoundaryBound) : Prop :=
  ∀ f : ZetaAdmissibleFunction,
    zetaCompletedZeroSideAnnihilator
      b hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary f = 0

end ZetaAdmissibleFunction
end
end LFunctions
end Boundary
