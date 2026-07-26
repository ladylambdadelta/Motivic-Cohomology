import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaZeroTail.WeightedTail.Annihilator.FiniteWindow.CoordinateDensity
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaZeroTail.WeightedTail.Annihilator.FiniteWindow.FiniteSupportTomography
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaZeroTail.WeightedTail.Annihilator.FiniteWindow.SummableDomination

/-!
# Paired finite-coordinate completed-zero detection

This file turns dense-coordinate detection of a nonzero bounded completed-zero
coefficient into a finite completed-zero window whose finite contribution
strictly dominates the complementary tail.
-/

namespace Boundary
namespace LFunctions
noncomputable section
namespace ZetaAdmissibleFunction
namespace FiniteWindow

open scoped ENNReal

theorem exists_zetaCompletedZeroSideAnnihilator_finiteWindow_dominates_complementaryTail_of_coordinateDensity
    (hbranch : Complex.BinetSecondFormulaBranchUniformTailAbsorption)
    (hpartialOneTwo : BoundaryLineOneAbelPartialMajorant)
    (hcompactOneTwo : PoleClearedOneTwoStripCompactBoundaryBound)
    (hfinite : PoleClearedRightCriticalStripAdmissibleGrowth)
    (hpartialLeft : ReflectedBoundaryAbelPartialMajorant)
    (hcompactBoundary : PoleClearedRightCriticalStripCompactBoundaryBound)
    (b : lp (fun rhoCoordinate : ZetaCompletedZeroCoordinate => ℂ) (∞ : ENNReal))
    (rho : ZetaCompletedZeroCoordinate)
    (hrho : b rho ≠ 0)
    (hdense :
      zetaCompletedZeroSideCoordinateL1Closure
          hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary =
        Set.univ) :
    ∃ (S : Finset ℂ)
      (hS : ∀ eta : ℂ, eta ∈ S → ZetaCompletedZero eta)
      (f : ZetaAdmissibleFunction),
      (rho : ℂ) ∈ S ∧
        norm (zetaCompletedZeroSideAnnihilatorComplementaryTail b S f) <
          norm (zetaCompletedZeroSideAnnihilatorFiniteWindow b S hS f) :=
  match
    exists_probe_detecting_nonzero_completedZeroCoefficient_of_coordinateDensity
      hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary
      b rho hrho hdense with
  | ⟨f, hannihilator⟩ =>
      match
        exists_finiteWindow_dominates_complementaryTail_of_annihilator_ne_zero
          b hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary
          f rho hannihilator with
      | ⟨S, hS, hrhoS, hdominates⟩ =>
          ⟨S, hS, f, hrhoS, hdominates⟩

end FiniteWindow
end ZetaAdmissibleFunction
end
end LFunctions
end Boundary
