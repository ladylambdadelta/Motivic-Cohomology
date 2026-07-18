import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaZeroTail.WeightedTail.KernelDensity.AtomicDistributionGeometry

/-!
# Tomography on one completed-zero ordinate fiber

After Fourier localization fixes the imaginary ordinate, the remaining
exponentials have distinct real exponents.  Finite Lagrange recombination of
their real-coordinate moments extracts each coefficient.
-/

namespace Boundary
namespace LFunctions
noncomputable section
namespace ZetaAdmissibleFunction

/-- Complexified real coordinates are injective on one completed-zero fiber. -/
theorem completedZeroImaginaryFiberFinset_complexReal_injective
    (height : ℝ) :
    Set.InjOn
      (fun rho : ZetaCompletedZeroCoordinate => ((rho : ℂ).re : ℂ))
      (completedZeroImaginaryFiberFinset height :
        Set ZetaCompletedZeroCoordinate) :=
  fun rho hrho eta heta hequal =>
    completedZeroImaginaryFiberFinset_real_injective height
      hrho
      heta
      (Complex.ofReal_injective hequal)

/-- Lagrange recombination extracts a selected coefficient from the
real-coordinate moments on one finite ordinate fiber. -/
theorem completedZeroImaginaryFiber_coefficient_eq_weighted_moments
    (height : ℝ)
    (coefficient : ZetaCompletedZeroCoordinate → ℂ)
    (rho : ZetaCompletedZeroCoordinate)
    (hrho : rho ∈ completedZeroImaginaryFiberFinset height) :
    ∃ weights : Fin (completedZeroImaginaryFiberFinset height).card → ℂ,
      (∑ k : Fin (completedZeroImaginaryFiberFinset height).card,
          weights k *
            (∑ eta in completedZeroImaginaryFiberFinset height,
              coefficient eta * (((eta : ℂ).re : ℂ) ^ (k : ℕ)))) =
        coefficient rho := by
  exact
    zetaFiniteExponentialMoments_lagrange_recombine_finset
      (s := completedZeroImaginaryFiberFinset height)
      (χ := fun eta : ZetaCompletedZeroCoordinate => ((eta : ℂ).re : ℂ))
      (seededCoeff := coefficient)
      (completedZeroImaginaryFiberFinset_complexReal_injective height)
      hrho

/-- If every real-coordinate moment on one completed-zero ordinate fiber
vanishes, every coefficient on that fiber is zero. -/
theorem completedZeroImaginaryFiber_coefficients_eq_zero_of_moments
    (height : ℝ)
    (coefficient : ZetaCompletedZeroCoordinate → ℂ)
    (hmoments :
      ∀ k : ℕ,
        (∑ rho in completedZeroImaginaryFiberFinset height,
          coefficient rho * (((rho : ℂ).re : ℂ) ^ k)) = 0) :
    ∀ rho : ZetaCompletedZeroCoordinate,
      rho ∈ completedZeroImaginaryFiberFinset height →
        coefficient rho = 0 := by
  intro rho hrho
  obtain ⟨weights, hextraction⟩ :=
    completedZeroImaginaryFiber_coefficient_eq_weighted_moments
      height coefficient rho hrho
  have hweightedZero :
      (∑ k : Fin (completedZeroImaginaryFiberFinset height).card,
          weights k *
            (∑ eta in completedZeroImaginaryFiberFinset height,
              coefficient eta * (((eta : ℂ).re : ℂ) ^ (k : ℕ)))) = 0 :=
    Finset.sum_eq_zero
      (fun k hk =>
        have hmoment :
            (∑ eta in completedZeroImaginaryFiberFinset height,
              coefficient eta * (((eta : ℂ).re : ℂ) ^ (k : ℕ))) = 0 :=
          hmoments (k : ℕ)
        Eq.trans
          (congrArg (fun value : ℂ => weights k * value) hmoment)
          (mul_zero (weights k)))
  exact Eq.trans hextraction.symm hweightedZero

/-- Fiberwise moment vanishing at every ordinate forces global coefficient
vanishing. -/
theorem completedZeroAtomic_coefficients_eq_zero_of_fiber_moments
    (coefficient : ZetaCompletedZeroCoordinate → ℂ)
    (hmoments :
      ∀ height : ℝ,
        ∀ k : ℕ,
          (∑ rho in completedZeroImaginaryFiberFinset height,
            coefficient rho * (((rho : ℂ).re : ℂ) ^ k)) = 0) :
    coefficient = 0 := by
  funext rho
  exact
    completedZeroImaginaryFiber_coefficients_eq_zero_of_moments
      (rho : ℂ).im
      coefficient
      (hmoments (rho : ℂ).im)
      rho
      (mem_completedZeroImaginaryFiberFinset_self rho)

end ZetaAdmissibleFunction
end
end LFunctions
end Boundary
