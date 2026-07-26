import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.OwnerParts.FiniteTomographyParts.QuantitativeSeparation.ControlledRightInverse

namespace Boundary
namespace LFunctions
noncomputable section
namespace ZetaAdmissibleFunction
namespace QuantitativeSeparation

theorem exists_fixedFiberProbe_with_autocorrelationZeroTailRealAbs_lt
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
        autocorrelationZeroTailRealAbs S f < epsilon :=
  match
    exists_fixedFiberProbe_with_completedZeroComplementL1Norm_lt
      hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary
      S P f₀ hSeparated epsilon hepsilon with
  | ⟨f, hfFiber, hweightedTail⟩ =>
      let hrealTail :
          autocorrelationZeroTailRealAbs S f < epsilon :=
        autocorrelationZeroTailRealAbs_lt_of_completedZeroComplementL1Norm_lt
          hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary
          S f epsilon hweightedTail
      ⟨f, hfFiber, hrealTail⟩

end QuantitativeSeparation
end ZetaAdmissibleFunction
end
end LFunctions
end Boundary
