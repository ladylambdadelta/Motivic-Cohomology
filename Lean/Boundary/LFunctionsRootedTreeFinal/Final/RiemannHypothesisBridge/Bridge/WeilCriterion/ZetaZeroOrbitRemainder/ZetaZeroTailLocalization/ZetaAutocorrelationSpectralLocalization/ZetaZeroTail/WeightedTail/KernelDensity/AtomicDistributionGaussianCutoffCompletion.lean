import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaZeroTail.WeightedTail.KernelDensity.AtomicDistributionGaussianCutoffUniformMajorant
import Mathlib.Analysis.Normed.Group.Tannery

/-!
# Compact Gaussian completion in weighted atomic norm

Natural compact Gaussian cutoffs, after normalized dilation, target modulation,
and the finite exceptional operator, converge to the corresponding full
Gaussian family in every polynomially weighted completed-zero atomic norm.
-/

namespace Boundary
namespace LFunctions
noncomputable section
namespace ZetaAdmissibleFunction

/-- The full Gaussian Laplace integrand is integrable at every complex
spectral parameter. -/
theorem integrable_physicalGaussian_mul_complexExponential
    (z : ℂ) :
    MeasureTheory.Integrable
      (fun t : ℝ =>
        physicalGaussian t * Complex.exp (z * (t : ℂ))) := by
  have hquadratic :
      MeasureTheory.Integrable
        (fun t : ℝ =>
          Complex.exp
            ((-(1 : ℂ)) * (t : ℂ) ^ 2 + z * (t : ℂ) + 0)) :=
    integrable_cexp_quadratic'
      (b := (-(1 : ℂ)))
      (show (-(1 : ℂ)).re < 0 from neg_lt_zero.mpr zero_lt_one)
      z
      0
  have hintegrand :
      (fun t : ℝ =>
        physicalGaussian t * Complex.exp (z * (t : ℂ))) =
      (fun t : ℝ =>
        Complex.exp
          ((-(1 : ℂ)) * (t : ℂ) ^ 2 + z * (t : ℂ) + 0)) := by
    funext t
    exact physicalGaussian_mul_exp_eq_quadraticExp z t
  exact Eq.mp
    (congrArg
      (fun integrand : ℝ → ℂ =>
        MeasureTheory.Integrable integrand MeasureTheory.volume)
      hintegrand.symm)
    hquadratic

/-- Every compact Gaussian Laplace integrand is bounded by the norm of the
corresponding full Gaussian Laplace integrand. -/
theorem admissibleGaussianCutoffNat_complexExponential_norm_le
    (n : ℕ)
    (z : ℂ)
    (t : ℝ) :
    ‖admissibleGaussianCutoffNat n t *
        Complex.exp (z * (t : ℂ))‖ ≤
      ‖physicalGaussian t * Complex.exp (z * (t : ℂ))‖ := by
  have hcutoff :
      ‖admissibleGaussianCutoffNat n t‖ ≤ ‖physicalGaussian t‖ :=
    admissibleGaussianCutoffNat_norm_le n t
  have hexponentialNonnegative :
      0 ≤ ‖Complex.exp (z * (t : ℂ))‖ :=
    norm_nonneg (Complex.exp (z * (t : ℂ)))
  have hproduct :
      ‖admissibleGaussianCutoffNat n t‖ *
          ‖Complex.exp (z * (t : ℂ))‖ ≤
        ‖physicalGaussian t‖ *
          ‖Complex.exp (z * (t : ℂ))‖ :=
    mul_le_mul_of_nonneg_right hcutoff hexponentialNonnegative
  exact Eq.subst
    (motive := fun left : ℝ =>
      left ≤ ‖physicalGaussian t * Complex.exp (z * (t : ℂ))‖)
    (norm_mul
      (admissibleGaussianCutoffNat n t)
      (Complex.exp (z * (t : ℂ)))).symm
    (Eq.subst
      (motive := fun right : ℝ =>
        ‖admissibleGaussianCutoffNat n t‖ *
            ‖Complex.exp (z * (t : ℂ))‖ ≤ right)
      (norm_mul
        (physicalGaussian t)
        (Complex.exp (z * (t : ℂ)))).symm
      hproduct)

/-- At every physical point, the compact Gaussian Laplace integrands are
eventually exactly the full Gaussian Laplace integrand. -/
theorem admissibleGaussianCutoffNat_complexExponential_eventually_eq
    (z : ℂ)
    (t : ℝ) :
    ∀ᶠ n : ℕ in Filter.atTop,
      admissibleGaussianCutoffNat n t * Complex.exp (z * (t : ℂ)) =
        physicalGaussian t * Complex.exp (z * (t : ℂ)) :=
  Filter.Eventually.mono
    (admissibleGaussianCutoffNat_eventually_eq t)
    (fun n hn =>
      congrArg
        (fun value : ℂ => value * Complex.exp (z * (t : ℂ)))
        hn)

/-- The full Gaussian integrand is eventually the compact Gaussian integrand. -/
theorem physicalGaussian_complexExponential_eventually_eq_cutoffNat
    (z : ℂ)
    (t : ℝ) :
    ∀ᶠ n : ℕ in Filter.atTop,
      physicalGaussian t * Complex.exp (z * (t : ℂ)) =
        admissibleGaussianCutoffNat n t * Complex.exp (z * (t : ℂ)) :=
  Filter.Eventually.mono
    (admissibleGaussianCutoffNat_complexExponential_eventually_eq z t)
    (fun n hn => hn.symm)

/-- Compact Gaussian Laplace transforms converge pointwise on the full
complex spectral plane to the exact full Gaussian kernel. -/
theorem integral_admissibleGaussianCutoffNat_mul_complexExponential_tendsto_full
    (z : ℂ) :
    Filter.Tendsto
      (fun n : ℕ =>
        ∫ t : ℝ,
          admissibleGaussianCutoffNat n t *
            Complex.exp (z * (t : ℂ)))
      Filter.atTop
      (nhds (fullGaussianLaplaceKernel z)) := by
  have hmeasurable :
      ∀ n : ℕ,
        MeasureTheory.AEStronglyMeasurable
          (fun t : ℝ =>
            admissibleGaussianCutoffNat n t *
              Complex.exp (z * (t : ℂ))) :=
    fun n =>
      ((admissibleGaussianCutoffNat n).toZetaTestFunction.continuous.mul
        (Complex.continuous_exp.comp
          (continuous_const.mul Complex.continuous_ofReal))).aestronglyMeasurable
  have hmajorantIntegrable :
      MeasureTheory.Integrable
        (fun t : ℝ =>
          ‖physicalGaussian t * Complex.exp (z * (t : ℂ))‖) :=
    (integrable_physicalGaussian_mul_complexExponential z).norm
  have hbound :
      ∀ n : ℕ,
        ∀ᵐ t : ℝ,
          ‖admissibleGaussianCutoffNat n t *
              Complex.exp (z * (t : ℂ))‖ ≤
            ‖physicalGaussian t * Complex.exp (z * (t : ℂ))‖ :=
    fun n =>
      Filter.Eventually.of_forall
        (admissibleGaussianCutoffNat_complexExponential_norm_le n z)
  have hpointwise :
      ∀ᵐ t : ℝ,
        Filter.Tendsto
          (fun n : ℕ =>
            admissibleGaussianCutoffNat n t *
              Complex.exp (z * (t : ℂ)))
          Filter.atTop
          (nhds
            (physicalGaussian t * Complex.exp (z * (t : ℂ)))) :=
    Filter.Eventually.of_forall
      (fun t =>
        Filter.Tendsto.congr'
          (physicalGaussian_complexExponential_eventually_eq_cutoffNat z t)
          tendsto_const_nhds)
  exact MeasureTheory.tendsto_integral_of_dominated_convergence
    (fun t : ℝ =>
      ‖physicalGaussian t * Complex.exp (z * (t : ℂ))‖)
    hmeasurable
    hmajorantIntegrable
    hbound
    hpointwise

/-- Spectral evaluations of compact Gaussian cutoffs converge at every
complex parameter to the full Gaussian Laplace kernel. -/
theorem zetaSpectralEval_admissibleGaussianCutoffNat_tendsto_full
    (z : ℂ) :
    Filter.Tendsto
      (fun n : ℕ =>
        zetaSpectralEval (admissibleGaussianCutoffNat n) z)
      Filter.atTop
      (nhds (fullGaussianLaplaceKernel z)) := by
  have hevaluation :
      ∀ n : ℕ,
        zetaSpectralEval (admissibleGaussianCutoffNat n) z =
          ∫ t : ℝ,
            admissibleGaussianCutoffNat n t *
              Complex.exp (z * (t : ℂ)) :=
    fun n =>
      zetaSpectralEval_eq_laplace
        (admissibleGaussianCutoffNat n)
        z
  exact Filter.Tendsto.congr'
    (Filter.Eventually.of_forall hevaluation)
    (integral_admissibleGaussianCutoffNat_mul_complexExponential_tendsto_full z)

/-- Polynomially weighted atomic sums of the concrete compact Gaussian probes
converge to the full scaled Gaussian atomic sum. -/
theorem completedZeroAtomic_targetScaledGaussianCutoff_tsum_tendsto_full
    (hbranch : Complex.BinetSecondFormulaBranchUniformTailAbsorption)
    (hpartialOneTwo : BoundaryLineOneAbelPartialMajorant)
    (hcompactOneTwo : PoleClearedOneTwoStripCompactBoundaryBound)
    (hfinite : PoleClearedRightCriticalStripAdmissibleGrowth)
    (hpartialLeft : ReflectedBoundaryAbelPartialMajorant)
    (hcompactBoundary : PoleClearedRightCriticalStripCompactBoundaryBound)
    (coefficient : ZetaCompletedZeroCoordinate → ℂ)
    (hgrowth : CompletedZeroAtomicPolynomialGrowth coefficient)
    (target : ZetaCompletedZeroCoordinate)
    (scale : ℝ)
    (hscale : 0 < scale) :
    Filter.Tendsto
      (fun n : ℕ =>
        ∑' rho : ZetaCompletedZeroCoordinate,
          coefficient rho *
            zetaSpectralEval
              (completedZeroTargetScaledGaussianCutoffProbe
                target scale n)
              (rho : ℂ))
      Filter.atTop
      (nhds
        (∑' rho : ZetaCompletedZeroCoordinate,
          completedZeroScaledGaussianAtomicTerm
            coefficient target scale rho)) := by
  obtain ⟨majorant, hmajorantSummable, hmajorantBound⟩ :=
    completedZeroTargetScaledGaussianCutoff_exists_summable_majorant
      hbranch hpartialOneTwo hcompactOneTwo hfinite
      hpartialLeft hcompactBoundary
      coefficient hgrowth target scale hscale
  have hpointwise :
      ∀ rho : ZetaCompletedZeroCoordinate,
        Filter.Tendsto
          (fun n : ℕ =>
            coefficient rho *
              zetaSpectralEval
                (completedZeroTargetScaledGaussianCutoffProbe
                  target scale n)
                (rho : ℂ))
          Filter.atTop
          (nhds
            (completedZeroScaledGaussianAtomicTerm
              coefficient target scale rho)) := by
    intro rho
    let spectralArgument : ℂ :=
      (scale : ℂ) * ((rho : ℂ) - (target : ℂ))
    let fixedMultiplier : ℂ :=
      coefficient rho *
        completedZeroTargetGaussianMultiplier target rho
    have hcutoff :
        Filter.Tendsto
          (fun n : ℕ =>
            zetaSpectralEval
              (admissibleGaussianCutoffNat n)
              spectralArgument)
          Filter.atTop
          (nhds (fullGaussianLaplaceKernel spectralArgument)) :=
      zetaSpectralEval_admissibleGaussianCutoffNat_tendsto_full
        spectralArgument
    have hmultiplied :
        Filter.Tendsto
          (fun n : ℕ =>
            fixedMultiplier *
              zetaSpectralEval
                (admissibleGaussianCutoffNat n)
                spectralArgument)
          Filter.atTop
          (nhds
            (fixedMultiplier *
              fullGaussianLaplaceKernel spectralArgument)) :=
      Filter.Tendsto.const_mul fixedMultiplier hcutoff
    have htermEquality :
        ∀ n : ℕ,
          coefficient rho *
              zetaSpectralEval
                (completedZeroTargetScaledGaussianCutoffProbe
                  target scale n)
                (rho : ℂ) =
            fixedMultiplier *
              zetaSpectralEval
                (admissibleGaussianCutoffNat n)
                spectralArgument := by
      intro n
      have hevaluation :=
        zetaSpectralEval_completedZeroTargetScaledGaussianCutoffProbe
          target rho scale hscale n
      exact Eq.trans
        (congrArg (fun value : ℂ => coefficient rho * value) hevaluation)
        (mul_assoc
          (coefficient rho)
          (completedZeroTargetGaussianMultiplier target rho)
          (zetaSpectralEval
            (admissibleGaussianCutoffNat n)
            spectralArgument)).symm
    have hlimitEquality :
        fixedMultiplier * fullGaussianLaplaceKernel spectralArgument =
          completedZeroScaledGaussianAtomicTerm
            coefficient target scale rho :=
      Eq.refl _
    exact Eq.subst
      (motive := fun limit : ℂ =>
        Filter.Tendsto
          (fun n : ℕ =>
            coefficient rho *
              zetaSpectralEval
                (completedZeroTargetScaledGaussianCutoffProbe
                  target scale n)
                (rho : ℂ))
          Filter.atTop
          (nhds limit))
      hlimitEquality
      (Filter.Tendsto.congr'
        (Filter.Eventually.of_forall (fun n => (htermEquality n).symm))
        hmultiplied)
  have huniformBound :
      ∀ᶠ n : ℕ in Filter.atTop,
        ∀ rho : ZetaCompletedZeroCoordinate,
          ‖coefficient rho *
              zetaSpectralEval
                (completedZeroTargetScaledGaussianCutoffProbe
                  target scale n)
                (rho : ℂ)‖ ≤
            majorant rho :=
    Filter.Eventually.of_forall hmajorantBound
  exact tendsto_tsum_of_dominated_convergence
    hmajorantSummable
    hpointwise
    huniformBound

end ZetaAdmissibleFunction
end
end LFunctions
end Boundary
