import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaZeroTail.WeightedTail.Annihilator.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ProbeInterface.ZetaAdmissibleFunction.ZetaAdmissibleComplexModulation

/-!
# Modulation orbit of a completed-zero distribution

Complex modulation translates every completed-zero spectral sample.  This file
owns the resulting shifted coefficient series and its exact identification with
the bounded completed-zero annihilator.
-/

namespace Boundary
namespace LFunctions
noncomputable section
namespace ZetaAdmissibleFunction

noncomputable def completedZeroShiftedAnnihilatorSeries
    (b : lp (fun rhoCoordinate : ZetaCompletedZeroCoordinate => ℂ) (∞ : ENNReal))
    (a : ℂ)
    (f : ZetaAdmissibleFunction)
    (rho : ZetaCompletedZeroCoordinate) : ℂ :=
  b rho *
    (-((zetaZeroMultiplicity (rho : ℂ) : ℂ)) *
      zetaSpectralEval f ((rho : ℂ) - a))

theorem completedZeroShiftedAnnihilatorSeries_eq_modulated_sideContribution
    (b : lp (fun rhoCoordinate : ZetaCompletedZeroCoordinate => ℂ) (∞ : ENNReal))
    (a : ℂ)
    (f : ZetaAdmissibleFunction)
    (rho : ZetaCompletedZeroCoordinate) :
    completedZeroShiftedAnnihilatorSeries b a f rho =
      b rho * zetaZeroSideContribution (rho : ℂ)
        (complexExponentialModulate a f) := by
  have hspectralTranslation :
      zetaSpectralEval (complexExponentialModulate a f) (rho : ℂ) =
        zetaSpectralEval f ((rho : ℂ) - a) :=
    zetaSpectralEval_complexExponentialModulate a (rho : ℂ) f
  unfold completedZeroShiftedAnnihilatorSeries
  unfold zetaZeroSideContribution
  exact congrArg
    (fun spectralValue : ℂ =>
      b rho *
        (-((zetaZeroMultiplicity (rho : ℂ) : ℂ)) * spectralValue))
    hspectralTranslation.symm

theorem summable_completedZeroShiftedAnnihilatorSeries
    (b : lp (fun rhoCoordinate : ZetaCompletedZeroCoordinate => ℂ) (∞ : ENNReal))
    (hbranch : Complex.BinetSecondFormulaBranchUniformTailAbsorption)
    (hpartialOneTwo : BoundaryLineOneAbelPartialMajorant)
    (hcompactOneTwo : PoleClearedOneTwoStripCompactBoundaryBound)
    (hfinite : PoleClearedRightCriticalStripAdmissibleGrowth)
    (hpartialLeft : ReflectedBoundaryAbelPartialMajorant)
    (hcompactBoundary : PoleClearedRightCriticalStripCompactBoundaryBound)
    (a : ℂ)
    (f : ZetaAdmissibleFunction) :
    Summable (completedZeroShiftedAnnihilatorSeries b a f) := by
  have hmodulatedSummable :
      Summable
        (fun rho : ZetaCompletedZeroCoordinate =>
          b rho * zetaZeroSideContribution (rho : ℂ)
            (complexExponentialModulate a f)) :=
    summable_zetaCompletedZeroSideAnnihilator
      b hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary
      (complexExponentialModulate a f)
  have hseriesEquality :
      completedZeroShiftedAnnihilatorSeries b a f =
        (fun rho : ZetaCompletedZeroCoordinate =>
          b rho * zetaZeroSideContribution (rho : ℂ)
            (complexExponentialModulate a f)) :=
    funext
      (fun rho : ZetaCompletedZeroCoordinate =>
        completedZeroShiftedAnnihilatorSeries_eq_modulated_sideContribution
          b a f rho)
  exact Eq.mpr (congrArg Summable hseriesEquality.symm) hmodulatedSummable

theorem zetaCompletedZeroSideAnnihilator_complexModulate_eq_shiftedSeries_tsum
    (b : lp (fun rhoCoordinate : ZetaCompletedZeroCoordinate => ℂ) (∞ : ENNReal))
    (hbranch : Complex.BinetSecondFormulaBranchUniformTailAbsorption)
    (hpartialOneTwo : BoundaryLineOneAbelPartialMajorant)
    (hcompactOneTwo : PoleClearedOneTwoStripCompactBoundaryBound)
    (hfinite : PoleClearedRightCriticalStripAdmissibleGrowth)
    (hpartialLeft : ReflectedBoundaryAbelPartialMajorant)
    (hcompactBoundary : PoleClearedRightCriticalStripCompactBoundaryBound)
    (a : ℂ)
    (f : ZetaAdmissibleFunction) :
    zetaCompletedZeroSideAnnihilator
        b hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary
        (complexExponentialModulate a f) =
      tsum (completedZeroShiftedAnnihilatorSeries b a f) := by
  have hannihilatorTsum :=
    zetaCompletedZeroSideAnnihilator_eq_tsum
      b hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary
      (complexExponentialModulate a f)
  have hseriesTsum :
      tsum
          (fun rho : ZetaCompletedZeroCoordinate =>
            b rho * zetaZeroSideContribution (rho : ℂ)
              (complexExponentialModulate a f)) =
        tsum (completedZeroShiftedAnnihilatorSeries b a f) :=
    tsum_congr
      (fun rho : ZetaCompletedZeroCoordinate =>
        (completedZeroShiftedAnnihilatorSeries_eq_modulated_sideContribution
          b a f rho).symm)
  exact Eq.trans hannihilatorTsum hseriesTsum

end ZetaAdmissibleFunction
end
end LFunctions
end Boundary
