import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.OwnerParts.FiniteTomographyParts.QuantitativeSeparation.WeightedTailNorm
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaAdmissibleSpectralLinearity

/-!
# Seed-dagger completed-zero product norm

The autocorrelation coordinate norm is expressed entirely in terms of the two
ordinary seed evaluations at `rho` and `-star rho`.
-/

namespace Boundary
namespace LFunctions
noncomputable section
namespace ZetaAdmissibleFunction
namespace QuantitativeSeparation

noncomputable def completedZeroSeedDaggerProductL1Norm
    (S : Finset ℂ)
    (f : ZetaAdmissibleFunction) : ℝ :=
  ∑' rho : {rho : ℂ // ZetaCompletedZero rho ∧ rho ∉ S},
    (zetaZeroMultiplicity (rho : ℂ) : ℝ) *
      (‖zetaSpectralEval f (rho : ℂ)‖ *
        ‖zetaSpectralEval f (-star (rho : ℂ))‖)

theorem completedZeroComplementL1Norm_convolutionAutocorrelation_eq_seedDaggerProduct
    (S : Finset ℂ)
    (f : ZetaAdmissibleFunction) :
    completedZeroComplementL1Norm S (convolutionAutocorrelation f) =
      completedZeroSeedDaggerProductL1Norm S f :=
  tsum_congr
    (fun rho : {rho : ℂ // ZetaCompletedZero rho ∧ rho ∉ S} =>
      let hcoordinate :
          zetaCompletedZeroAutocorrelationSideCoordinate f
              (⟨(rho : ℂ), rho.2.1⟩ : {rho : ℂ // ZetaCompletedZero rho}) =
            zetaZeroSideContribution (rho : ℂ) (convolutionAutocorrelation f) :=
        zetaCompletedZeroAutocorrelationSideCoordinate_eq f
          (⟨(rho : ℂ), rho.2.1⟩ : {rho : ℂ // ZetaCompletedZero rho})
      let hcoordinateNorm :
          ‖zetaCompletedZeroAutocorrelationSideCoordinate f
              (⟨(rho : ℂ), rho.2.1⟩ : {rho : ℂ // ZetaCompletedZero rho})‖ =
            ‖zetaSpectralEval f (rho : ℂ)‖ *
              ‖zetaSpectralEval f (-star (rho : ℂ))‖ :=
        norm_zetaCompletedZeroAutocorrelationSideCoordinate f
          (⟨(rho : ℂ), rho.2.1⟩ : {rho : ℂ // ZetaCompletedZero rho})
      Eq.trans
        (congrArg norm hcoordinate.symm)
        hcoordinateNorm)

end QuantitativeSeparation
end ZetaAdmissibleFunction
end
end LFunctions
end Boundary
