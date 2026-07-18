import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaZeroTail.WeightedTail.Annihilator.DistributionalClassification.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaZeroTail.WeightedTail.Annihilator.FiniteWindow.Core
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaZeroTail.WeightedTail.Annihilator.FiniteWindow.Detection

/-!
# Finite-window completed-zero annihilator assembly

This owner turns the paired finite-coordinate detection theorem into
coefficientwise uniqueness for bounded completed-zero distributions.
-/

namespace Boundary
namespace LFunctions
noncomputable section
namespace ZetaAdmissibleFunction
namespace FiniteWindow

theorem zetaCompletedZeroSideAnnihilator_ne_zero_of_finiteWindow_dominates_complementaryTail
    (b : lp (fun rhoCoordinate : ZetaCompletedZeroCoordinate => ℂ) (∞ : ENNReal))
    (hbranch : Complex.BinetSecondFormulaBranchUniformTailAbsorption)
    (hpartialOneTwo : BoundaryLineOneAbelPartialMajorant)
    (hcompactOneTwo : PoleClearedOneTwoStripCompactBoundaryBound)
    (hfinite : PoleClearedRightCriticalStripAdmissibleGrowth)
    (hpartialLeft : ReflectedBoundaryAbelPartialMajorant)
    (hcompactBoundary : PoleClearedRightCriticalStripCompactBoundaryBound)
    (S : Finset ℂ)
    (hS : ∀ eta : ℂ, eta ∈ S → ZetaCompletedZero eta)
    (f : ZetaAdmissibleFunction)
    (hdominates :
      norm (zetaCompletedZeroSideAnnihilatorComplementaryTail b S f) <
        norm (zetaCompletedZeroSideAnnihilatorFiniteWindow b S hS f) ) :
    zetaCompletedZeroSideAnnihilator
      b hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary f ≠ 0 := by
  intro hannihilates
  have hwindowEqNegTail :
      zetaCompletedZeroSideAnnihilatorFiniteWindow b S hS f =
        - zetaCompletedZeroSideAnnihilatorComplementaryTail b S f :=
    zetaCompletedZeroSideAnnihilatorFiniteWindow_eq_neg_complementaryTail_of_annihilates
      b hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary
      S hS f hannihilates
  have hnormEq :
      norm (zetaCompletedZeroSideAnnihilatorComplementaryTail b S f) =
        norm (zetaCompletedZeroSideAnnihilatorFiniteWindow b S hS f) := by
    calc
      norm (zetaCompletedZeroSideAnnihilatorComplementaryTail b S f) =
          norm (- zetaCompletedZeroSideAnnihilatorComplementaryTail b S f) :=
        (norm_neg (zetaCompletedZeroSideAnnihilatorComplementaryTail b S f)).symm
      norm (- zetaCompletedZeroSideAnnihilatorComplementaryTail b S f) =
          norm (zetaCompletedZeroSideAnnihilatorFiniteWindow b S hS f) :=
        congrArg norm hwindowEqNegTail.symm
  exact (not_lt_of_ge (le_of_eq hnormEq)) hdominates

/-- Finite-window detection of every nonzero coefficient turns probewise
annihilation into coefficientwise uniqueness. -/
theorem zetaCompletedZeroSideAnnihilator_coefficient_eq_zero_of_vanishes
    (hbranch : Complex.BinetSecondFormulaBranchUniformTailAbsorption)
    (hpartialOneTwo : BoundaryLineOneAbelPartialMajorant)
    (hcompactOneTwo : PoleClearedOneTwoStripCompactBoundaryBound)
    (hfinite : PoleClearedRightCriticalStripAdmissibleGrowth)
    (hpartialLeft : ReflectedBoundaryAbelPartialMajorant)
    (hcompactBoundary : PoleClearedRightCriticalStripCompactBoundaryBound)
    (b : lp (fun rhoCoordinate : ZetaCompletedZeroCoordinate => ℂ) (∞ : ENNReal))
    (hvanishes :
      ZetaCompletedZeroSideAnnihilatorVanishes
        b hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary) :
    b = 0 := by
  apply lp.ext
  funext rho
  by_contra hrho
  obtain ⟨S, hS, f, hrhoMem, hdominates⟩ :=
    exists_zetaCompletedZeroSideAnnihilator_finiteWindow_dominates_complementaryTail
      hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary
      b rho hrho
  exact
    zetaCompletedZeroSideAnnihilator_ne_zero_of_finiteWindow_dominates_complementaryTail
      b hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary
      S hS f hdominates
      (hvanishes f)

end FiniteWindow
end ZetaAdmissibleFunction
end
end LFunctions
end Boundary
