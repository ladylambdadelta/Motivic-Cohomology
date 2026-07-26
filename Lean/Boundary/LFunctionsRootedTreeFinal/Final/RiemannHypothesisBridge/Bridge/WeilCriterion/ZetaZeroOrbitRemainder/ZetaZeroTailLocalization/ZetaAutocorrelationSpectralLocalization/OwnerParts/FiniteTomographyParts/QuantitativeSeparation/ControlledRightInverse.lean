import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.OwnerParts.Presentation
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.OwnerParts.FiniteTomographyParts.QuantitativeSeparation.WeightedTailNorm
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.OwnerParts.FiniteTomographyParts.QuantitativeSeparation.SeedDaggerApproximation

/-!
# Controlled completed-zero fixed-fiber probes

This file owns the nonlinear density construction in the weighted completed-
zero coordinate norm.  It preserves the prescribed dagger fiber while making
the complementary autocorrelation coordinates arbitrarily small in `l1`.
-/

namespace Boundary
namespace LFunctions
noncomputable section
namespace ZetaAdmissibleFunction
namespace QuantitativeSeparation

theorem exists_fixedFiberProbe_with_completedZeroComplementL1Norm_lt
    (hbranch : Complex.BinetSecondFormulaBranchUniformTailAbsorption)
    (hpartialOneTwo : BoundaryLineOneAbelPartialMajorant)
    (hcompactOneTwo : PoleClearedOneTwoStripCompactBoundaryBound)
    (hfinite : PoleClearedRightCriticalStripAdmissibleGrowth)
    (hpartialLeft : ReflectedBoundaryAbelPartialMajorant)
    (hcompactBoundary : PoleClearedRightCriticalStripCompactBoundaryBound)
    (S : Finset ℂ)
    (P : Finset ℂ)
    (f₀ : ZetaAdmissibleFunction)
    (hSeparated :
      ∀ rho : ℂ,
        ZetaCompletedZero rho →
          rho ∉ S →
            rho ∉ daggerClosedSpectralSampleFinset P)
    (epsilon : ℝ)
    (hepsilon : 0 < epsilon) :
    ∃ f : ZetaAdmissibleFunction,
      f ∈ AutocorrelationSpectralEvalFiberOf P f₀ ∧
        completedZeroComplementL1Norm S (convolutionAutocorrelation f) < epsilon :=
  match
    exists_fixedFiberProbe_with_seedDaggerProductL1Norm_lt
      hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary
      S P f₀ hSeparated epsilon hepsilon with
  | ⟨f, hfFiber, hseedDagger⟩ =>
      let hnormEquality :
          completedZeroComplementL1Norm S (convolutionAutocorrelation f) =
            completedZeroSeedDaggerProductL1Norm S f :=
        completedZeroComplementL1Norm_convolutionAutocorrelation_eq_seedDaggerProduct
          S f
      let htail :
          completedZeroComplementL1Norm S (convolutionAutocorrelation f) < epsilon :=
        Eq.subst
          (motive := fun value : ℝ => value < epsilon)
          hnormEquality.symm
          hseedDagger
      ⟨f, hfFiber, htail⟩

end QuantitativeSeparation
end ZetaAdmissibleFunction
end
end LFunctions
end Boundary
