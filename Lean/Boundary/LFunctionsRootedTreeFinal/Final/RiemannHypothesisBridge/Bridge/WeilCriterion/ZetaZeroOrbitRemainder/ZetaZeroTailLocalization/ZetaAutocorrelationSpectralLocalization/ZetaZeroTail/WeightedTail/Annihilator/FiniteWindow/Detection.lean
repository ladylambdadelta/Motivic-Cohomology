import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaZeroTail.WeightedTail.Annihilator.FiniteWindow.FiniteSupportTomography
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaZeroTail.WeightedTail.Annihilator.FiniteWindow.SummableDomination
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaZeroTail.WeightedTail.Annihilator.DistributionalClassification.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaTransformCalculus.Owner

/-!
# Paired finite-coordinate completed-zero detection

This file owns the analytic separation statement for a nonzero bounded
completed-zero coefficient distribution.  Its finite test must preserve the
completed-zero coordinate bookkeeping used by the explicit formula while its
finite pairing dominates the complementary tail.
-/

namespace Boundary
namespace LFunctions
noncomputable section
namespace ZetaAdmissibleFunction
namespace FiniteWindow

theorem exists_zetaCompletedZeroSideAnnihilator_finiteWindow_dominates_complementaryTail
    (hbranch : Complex.BinetSecondFormulaBranchUniformTailAbsorption)
    (hpartialOneTwo : BoundaryLineOneAbelPartialMajorant)
    (hcompactOneTwo : PoleClearedOneTwoStripCompactBoundaryBound)
    (hfinite : PoleClearedRightCriticalStripAdmissibleGrowth)
    (hpartialLeft : ReflectedBoundaryAbelPartialMajorant)
    (hcompactBoundary : PoleClearedRightCriticalStripCompactBoundaryBound)
    (b : lp (fun rhoCoordinate : ZetaCompletedZeroCoordinate => ℂ) (∞ : ENNReal))
    (rho : ZetaCompletedZeroCoordinate)
    (hrho : b rho ≠ 0) :
    ∃ (S : Finset ℂ)
      (hS : ∀ eta : ℂ, eta ∈ S → ZetaCompletedZero eta)
      (f : ZetaAdmissibleFunction),
      (rho : ℂ) ∈ S ∧
        norm (zetaCompletedZeroSideAnnihilatorComplementaryTail b S f) <
          norm (zetaCompletedZeroSideAnnihilatorFiniteWindow b S hS f) := by
  obtain ⟨f, hannihilator⟩ :=
    exists_probe_detecting_nonzero_completedZeroCoefficient
      hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary
      b rho hrho
  obtain ⟨S, hS, hrhoS, hdominates⟩ :=
    exists_finiteWindow_dominates_complementaryTail_of_annihilator_ne_zero
      b hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary
      f rho hannihilator
  exact ⟨S, hS, f, hrhoS, hdominates⟩

end FiniteWindow
end ZetaAdmissibleFunction
end
end LFunctions
end Boundary
