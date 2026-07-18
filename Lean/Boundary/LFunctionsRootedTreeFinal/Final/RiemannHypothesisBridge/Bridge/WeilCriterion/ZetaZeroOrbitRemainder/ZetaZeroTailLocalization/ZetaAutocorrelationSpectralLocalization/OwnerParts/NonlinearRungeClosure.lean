import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.OwnerParts.FiniteTomographyParts.Part02_TailTransport

namespace Boundary
namespace LFunctions
noncomputable section
namespace ZetaAdmissibleFunction

/-- Fixed-fiber nonlinear Runge closure follows from quantitative finite tomography. -/
theorem autocorrelationSpectralEvalFiber_zeroTailClosure_nonlinear_owner :
    AutocorrelationSpectralEvalFiberZeroTailClosureRunge := by
  intro hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary
  intro S P f₀ hSeparated
  exact
    autocorrelationSpectralEvalFiber_zeroTailRealAbsValues_zero_mem_closure_of_has_arbitrarily_small_values
      S P f₀
      (autocorrelationSpectralEvalFiber_zeroTailRealAbsValues_has_arbitrarily_small_values_of_nonDaggerHeightWindowTailLocalization
        hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary
        autocorrelationSpectralEvalFiber_separatedNonDaggerHeightWindowTailLocalization
        S P f₀ hSeparated)

end ZetaAdmissibleFunction
end
end LFunctions
end Boundary
