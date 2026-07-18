import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.OwnerParts.FiniteTomographyParts.QuantitativeSeparation.Owner

/-!
# Diagonal cardinal selection

Compatibility export for the controlled completed-zero right-inverse owner.
-/

namespace Boundary
namespace LFunctions
noncomputable section
namespace ZetaAdmissibleFunction

theorem exists_autocorrelationSpectralEvalFiber_diagonalCardinalTail_lt
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
        autocorrelationZeroTailRealAbs S f < epsilon := by
  exact
    QuantitativeSeparation.exists_fixedFiberProbe_with_autocorrelationZeroTailRealAbs_lt
      hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary
      S P f₀ hSeparated epsilon hepsilon

end ZetaAdmissibleFunction
end
end LFunctions
end Boundary
