import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaZeroTail.WeightedTail.Annihilator.FiniteWindow.Owner

/-!
# Density finite-window carrier gap wrappers

This file re-exports the finite-window quantitative carrier gap in the density
owner namespace.
-/

namespace Boundary
namespace LFunctions
noncomputable section
namespace ZetaAdmissibleFunction

open scoped ENNReal
open FiniteWindow

theorem zetaCompletedZeroSideAnnihilator_complementaryTail_norm_eq_finiteWindow_norm
    (b : lp (fun rhoCoordinate : ZetaCompletedZeroCoordinate => ℂ) (∞ : ENNReal))
    (S : Finset ℂ)
    (hS : ∀ eta : ℂ, eta ∈ S → ZetaCompletedZero eta)
    (f : ZetaAdmissibleFunction)
    (hwindowEqNegTail :
      zetaCompletedZeroSideAnnihilatorFiniteWindow b S hS f =
        - zetaCompletedZeroSideAnnihilatorComplementaryTail b S f) :
    norm (zetaCompletedZeroSideAnnihilatorComplementaryTail b S f) =
      norm (zetaCompletedZeroSideAnnihilatorFiniteWindow b S hS f) :=
  FiniteWindow.norm_eq_of_eq_neg_complex
    (zetaCompletedZeroSideAnnihilatorComplementaryTail b S f)
    (zetaCompletedZeroSideAnnihilatorFiniteWindow b S hS f)
    hwindowEqNegTail

theorem not_lt_of_eq_real
    (x : ℝ)
    (y : ℝ)
    (hxy : x = y) :
    ¬ x < y :=
  not_lt_of_ge (le_of_eq hxy.symm)

/-- Strict finite-window domination of the complementary tail forces the
bounded completed-zero annihilator to be nonzero on that probe. -/
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
      b hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary f ≠ 0 :=
  FiniteWindow.zetaCompletedZeroSideAnnihilator_ne_zero_of_finiteWindow_dominates_complementaryTail
    b hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary
    S hS f hdominates

/-- A nonzero bounded completed-zero coefficient can be detected on a finite
zero window with a positive quantitative gap between the finite-window carrier
and the complementary tail. -/
theorem exists_zetaCompletedZeroSideAnnihilator_finiteWindow_gap_bound
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
      (f : ZetaAdmissibleFunction)
      (carrierBound : ℝ)
      (carrierGap : ℝ),
      (rho : ℂ) ∈ S ∧
        0 < carrierBound ∧
          0 < carrierGap ∧
            carrierBound =
                norm (zetaCompletedZeroSideAnnihilatorFiniteWindow b S hS f) ∧
              norm (zetaCompletedZeroSideAnnihilatorComplementaryTail b S f) +
                  carrierGap ≤
                carrierBound :=
  FiniteWindow.exists_zetaCompletedZeroSideAnnihilator_quantitativeCarrierSeparation_with_gap
    hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary
    b rho hrho

/-- A nonzero bounded completed-zero coefficient has a finite carrier and a
positive constant that is bounded above by the norm of the full annihilator on
the selected probe. -/
theorem exists_zetaCompletedZeroSideAnnihilator_finiteWindow_constant_bound
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
      (f : ZetaAdmissibleFunction)
      (carrierBound : ℝ)
      (carrierGap : ℝ),
      (rho : ℂ) ∈ S ∧
        0 < carrierBound ∧
          0 < carrierGap ∧
            carrierBound =
                norm (zetaCompletedZeroSideAnnihilatorFiniteWindow b S hS f) ∧
              norm (zetaCompletedZeroSideAnnihilatorComplementaryTail b S f) +
                  carrierGap ≤
                carrierBound ∧
                carrierGap ≤
                  norm
                    (zetaCompletedZeroSideAnnihilator
                      b hbranch hpartialOneTwo hcompactOneTwo hfinite
                        hpartialLeft hcompactBoundary f) :=
  FiniteWindow.exists_zetaCompletedZeroSideAnnihilator_quantitativeCarrierSeparation_constant_bound
    hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary
    b rho hrho

/-- A nonzero bounded completed-zero coefficient yields a finite carrier and
an admissible probe on which the full annihilator has a positive norm lower
bound. -/
theorem exists_zetaCompletedZeroSideAnnihilator_positive_norm_lower_bound_with_carrier
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
      (f : ZetaAdmissibleFunction)
      (constant : ℝ),
      (rho : ℂ) ∈ S ∧
        0 < constant ∧
          constant ≤
            norm
              (zetaCompletedZeroSideAnnihilator
                b hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft
                  hcompactBoundary f) :=
  FiniteWindow.exists_zetaCompletedZeroSideAnnihilator_positive_norm_lower_bound_with_carrier
    hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary
    b rho hrho

/-- A nonzero bounded completed-zero coefficient yields an admissible probe on
which the full annihilator has a positive norm lower bound. -/
theorem exists_zetaCompletedZeroSideAnnihilator_positive_norm_lower_bound
    (hbranch : Complex.BinetSecondFormulaBranchUniformTailAbsorption)
    (hpartialOneTwo : BoundaryLineOneAbelPartialMajorant)
    (hcompactOneTwo : PoleClearedOneTwoStripCompactBoundaryBound)
    (hfinite : PoleClearedRightCriticalStripAdmissibleGrowth)
    (hpartialLeft : ReflectedBoundaryAbelPartialMajorant)
    (hcompactBoundary : PoleClearedRightCriticalStripCompactBoundaryBound)
    (b : lp (fun rhoCoordinate : ZetaCompletedZeroCoordinate => ℂ) (∞ : ENNReal))
    (rho : ZetaCompletedZeroCoordinate)
    (hrho : b rho ≠ 0) :
    ∃ (f : ZetaAdmissibleFunction)
      (constant : ℝ),
      0 < constant ∧
        constant ≤
          norm
            (zetaCompletedZeroSideAnnihilator
              b hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft
                hcompactBoundary f) :=
  FiniteWindow.exists_zetaCompletedZeroSideAnnihilator_positive_norm_lower_bound
    hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary
    b rho hrho

/-- A positive finite-window gap forces the bounded completed-zero
annihilator to be nonzero on that probe. -/
theorem zetaCompletedZeroSideAnnihilator_ne_zero_of_finiteWindow_gap_bound
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
    (carrierGap : ℝ)
    (hcarrierGapPositive : 0 < carrierGap)
    (htailGapLe :
      norm (zetaCompletedZeroSideAnnihilatorComplementaryTail b S f) +
          carrierGap ≤
        norm (zetaCompletedZeroSideAnnihilatorFiniteWindow b S hS f)) :
    zetaCompletedZeroSideAnnihilator
      b hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary f ≠ 0 :=
  FiniteWindow.zetaCompletedZeroSideAnnihilator_ne_zero_of_finiteWindow_gap_bound
    b hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary
    S hS f carrierGap hcarrierGapPositive htailGapLe

end ZetaAdmissibleFunction
end
end LFunctions
end Boundary
