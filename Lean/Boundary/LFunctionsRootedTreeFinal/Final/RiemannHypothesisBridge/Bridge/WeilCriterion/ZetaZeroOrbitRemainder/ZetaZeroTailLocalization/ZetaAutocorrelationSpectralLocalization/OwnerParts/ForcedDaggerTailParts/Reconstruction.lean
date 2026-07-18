import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.OwnerParts.ForcedDaggerTailParts.Core
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.OwnerParts.NonlinearRungeClosure
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.OwnerParts.PresentationParts.Part02_FiberDensity

namespace Boundary
namespace LFunctions
noncomputable section
namespace ZetaAdmissibleFunction

/-- The direct finite-window selector yields arbitrarily small realized raw
zero-tail values in each separated autocorrelation spectral fiber. -/
theorem autocorrelationSpectralEvalFiberDirectCenteredZeroTailSmallValuesRunge_owner :
    ∀ (hbranch : Complex.BinetSecondFormulaBranchUniformTailAbsorption)
      (hpartialOneTwo : BoundaryLineOneAbelPartialMajorant)
      (hcompactOneTwo : PoleClearedOneTwoStripCompactBoundaryBound)
      (hfinite : PoleClearedRightCriticalStripAdmissibleGrowth)
      (hpartialLeft : ReflectedBoundaryAbelPartialMajorant)
      (hcompactBoundary : PoleClearedRightCriticalStripCompactBoundaryBound),
      ∀ S : Finset ℂ, ∀ P : Finset ℂ, ∀ f₀ : ZetaAdmissibleFunction,
        (∀ ρ : ℂ, ZetaCompletedZero ρ → ρ ∉ S →
          ρ ∉ daggerClosedSpectralSampleFinset P) →
        ∀ ε : ℝ, 0 < ε →
          ∃ r : ℝ,
            r ∈ autocorrelationSpectralEvalFiberZeroTailRealAbsValues S P f₀ ∧
              r < ε := by
  intro hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary
  intro S P f₀ hSeparated ε hε
  have hclosure :
      (0 : ℝ) ∈ closure (autocorrelationSpectralEvalFiberZeroTailRealAbsValues S P f₀) :=
    autocorrelationSpectralEvalFiber_zeroTailClosure_nonlinear_owner
      hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary
      S P f₀ hSeparated
  exact
    autocorrelationSpectralEvalFiber_zeroTailRealAbsValues_has_arbitrarily_small_values_of_zero_mem_closure
      S P f₀ hclosure ε hε

end ZetaAdmissibleFunction
end
end LFunctions
end Boundary
