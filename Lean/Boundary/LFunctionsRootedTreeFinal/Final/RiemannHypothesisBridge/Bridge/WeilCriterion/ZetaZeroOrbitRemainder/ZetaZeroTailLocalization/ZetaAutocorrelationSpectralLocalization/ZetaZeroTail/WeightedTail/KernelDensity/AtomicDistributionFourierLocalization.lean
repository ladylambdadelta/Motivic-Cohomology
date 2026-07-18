import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaZeroTail.WeightedTail.KernelDensity.AtomicDistributionGrowth
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaZeroTail.WeightedTail.KernelDensity.AtomicDistributionGaussianLocalization
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaAdmissibleSpectralInterpolation.ZetaAdmissibleInterpolation.ZetaAdmissibleProbe.Owner

/-!
# Fourier localization of completed-zero atomic distributions

A polynomial-growth completed-zero coefficient family defines a distribution
on compactly supported smooth physical probes.  Fourier localization at one
imaginary ordinate leaves a finite fiber; differentiation in the physical
variable then gives every real-coordinate moment on that fiber.
-/

namespace Boundary
namespace LFunctions
noncomputable section
namespace ZetaAdmissibleFunction

/-- Fourier localization converts global annihilation of a polynomial-growth
completed-zero atomic Laplace distribution into finite real-coordinate moment
vanishing on every exact imaginary fiber. -/
theorem completedZeroAtomicLaplaceDistribution_fiber_moments_eq_zero
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
    ∀ height : ℝ,
      ∀ degree : ℕ,
        (∑ rho in completedZeroImaginaryFiberFinset height,
          coefficient rho * (((rho : ℂ).re : ℂ) ^ degree)) = 0 := by
  intro height degree
  exact Finset.sum_eq_zero
    (fun rho hrho =>
      have hcoefficient : coefficient rho = 0 :=
        completedZeroAtomicLaplaceDistribution_coefficient_eq_zero_at
          hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary
          coefficient hgrowth hsummable hvanishing rho
      Eq.trans
        (congrArg
          (fun value : ℂ =>
            value * (((rho : ℂ).re : ℂ) ^ degree))
          hcoefficient)
        (zero_mul (((rho : ℂ).re : ℂ) ^ degree)))

end ZetaAdmissibleFunction
end
end LFunctions
end Boundary
