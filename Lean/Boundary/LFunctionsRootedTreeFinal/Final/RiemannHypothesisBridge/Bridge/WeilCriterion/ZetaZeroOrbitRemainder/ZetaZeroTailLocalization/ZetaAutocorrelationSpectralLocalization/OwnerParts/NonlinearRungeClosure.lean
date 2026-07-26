import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.OwnerParts.FiniteTomographyParts.Part02_TailTransport

namespace Boundary
namespace LFunctions
noncomputable section
namespace ZetaAdmissibleFunction

/-- Fixed-fiber nonlinear Runge closure follows from quantitative finite tomography. -/
theorem autocorrelationSpectralEvalFiber_zeroTailClosure_nonlinear_owner :
    AutocorrelationSpectralEvalFiberZeroTailClosureRunge :=
  fun hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary =>
    fun S P f₀ hSeparated =>
      let hSmall :
          ∀ ε : ℝ, 0 < ε →
            ∃ r : ℝ,
              r ∈ autocorrelationSpectralEvalFiberZeroTailRealAbsValues S P f₀ ∧
                r < ε :=
        autocorrelationSpectralEvalFiber_zeroTailRealAbsValues_has_arbitrarily_small_values_of_nonDaggerHeightWindowTailLocalization
          hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary
          autocorrelationSpectralEvalFiber_separatedNonDaggerHeightWindowTailLocalization
          S P f₀ hSeparated
      show
        (0 : ℝ) ∈
          closure (autocorrelationSpectralEvalFiberZeroTailRealAbsValues S P f₀)
      from
        autocorrelationSpectralEvalFiber_zeroTailRealAbsValues_zero_mem_closure_of_has_arbitrarily_small_values
          S P f₀ hSmall

end ZetaAdmissibleFunction
end
end LFunctions
end Boundary
