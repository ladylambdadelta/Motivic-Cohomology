import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaZeroTail.WeightedTail.KernelDensity.AtomicDistributionFourierLocalization

/-!
# Uniqueness of completed-zero atomic Laplace distributions

A coefficient family whose atomic Laplace series is absolutely convergent on
every admissible probe defines a distribution on the physical test-function
space.  Vanishing on every admissible probe forces every atomic coefficient to
vanish.
-/

namespace Boundary
namespace LFunctions
noncomputable section
namespace ZetaAdmissibleFunction

theorem completedZeroAtomicLaplaceDistribution_coefficients_eq_zero
    (hbranch : Complex.BinetSecondFormulaBranchUniformTailAbsorption)
    (hpartialOneTwo : BoundaryLineOneAbelPartialMajorant)
    (hcompactOneTwo : PoleClearedOneTwoStripCompactBoundaryBound)
    (hfinite : PoleClearedRightCriticalStripAdmissibleGrowth)
    (hpartialLeft : ReflectedBoundaryAbelPartialMajorant)
    (hcompactBoundary : PoleClearedRightCriticalStripCompactBoundaryBound)
    (coefficient : ZetaCompletedZeroCoordinate → ℂ)
    (hgrowth : CompletedZeroAtomicPolynomialGrowth coefficient)
    (hsummable :
      ∀ f : ZetaAdmissibleFunction,
        Summable
          (fun rho : ZetaCompletedZeroCoordinate =>
            coefficient rho * zetaSpectralEval f (rho : ℂ)))
    (hvanishing :
      ∀ f : ZetaAdmissibleFunction,
        (∑' rho : ZetaCompletedZeroCoordinate,
          coefficient rho * zetaSpectralEval f (rho : ℂ)) = 0) :
    coefficient = 0 := by
  have hfiberMoments :
      ∀ height : ℝ,
        ∀ degree : ℕ,
          (∑ rho in completedZeroImaginaryFiberFinset height,
            coefficient rho * (((rho : ℂ).re : ℂ) ^ degree)) = 0 :=
    completedZeroAtomicLaplaceDistribution_fiber_moments_eq_zero
      hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary
      coefficient hgrowth hsummable hvanishing
  exact
    completedZeroAtomic_coefficients_eq_zero_of_fiber_moments
      coefficient hfiberMoments

end ZetaAdmissibleFunction
end
end LFunctions
end Boundary
