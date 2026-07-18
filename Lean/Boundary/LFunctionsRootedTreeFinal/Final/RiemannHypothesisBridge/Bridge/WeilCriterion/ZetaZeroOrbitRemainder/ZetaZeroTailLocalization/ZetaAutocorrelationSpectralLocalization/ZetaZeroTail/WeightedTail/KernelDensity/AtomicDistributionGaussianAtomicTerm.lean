import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaZeroTail.WeightedTail.KernelDensity.AtomicDistributionRapidDecaySummability
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaZeroTail.WeightedTail.KernelDensity.PolynomialMultiplierGrowth
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaZeroTail.WeightedTail.KernelDensity.AtomicDistributionExceptionalWindow

/-!
# Scaled Gaussian completed-zero atomic terms

This file owns the finite exceptional multiplier, the corresponding scaled
Gaussian atomic family, and its absolute summability.
-/

namespace Boundary
namespace LFunctions
noncomputable section
namespace ZetaAdmissibleFunction

/-- The finite radius-two multiplier centered at one target zero. -/
noncomputable def completedZeroTargetGaussianMultiplier
    (target rho : ZetaCompletedZeroCoordinate) : ℂ :=
  ((completedZeroTargetExceptionalValues target 2 zero_le_two).toList.map
    (fun sample : ℂ => sample - (rho : ℂ))).prod

/-- One term of the scaled full-Gaussian atomic identity. -/
noncomputable def completedZeroScaledGaussianAtomicTerm
    (coefficient : ZetaCompletedZeroCoordinate → ℂ)
    (target : ZetaCompletedZeroCoordinate)
    (scale : ℝ)
    (rho : ZetaCompletedZeroCoordinate) : ℂ :=
  coefficient rho * completedZeroTargetGaussianMultiplier target rho *
    fullGaussianLaplaceKernel
      ((scale : ℂ) * ((rho : ℂ) - (target : ℂ)))

/-- The nontarget part of the scaled full-Gaussian atomic identity. -/
noncomputable def completedZeroScaledGaussianAtomicTail
    (coefficient : ZetaCompletedZeroCoordinate → ℂ)
    (target : ZetaCompletedZeroCoordinate)
    (scale : ℝ) : ℂ :=
  ∑' rho : ZetaCompletedZeroCoordinate,
    if rho = target then 0
    else completedZeroScaledGaussianAtomicTerm coefficient target scale rho

/-- The radius-two target multiplier vanishes at every nearby nontarget
completed zero. -/
theorem completedZeroTargetGaussianMultiplier_eq_zero_of_near_of_ne
    (target rho : ZetaCompletedZeroCoordinate)
    (hnear : |(rho : ℂ).im - (target : ℂ).im| ≤ 2)
    (hne : rho ≠ target) :
    completedZeroTargetGaussianMultiplier target rho = 0 := by
  have hmembership :
      (rho : ℂ) ∈ completedZeroTargetExceptionalValues target 2 zero_le_two :=
    mem_completedZeroTargetExceptionalValues_of_near_of_ne
      target 2 zero_le_two rho hnear hne
  exact List.prod_eq_zero
    (List.mem_map.mpr
      ⟨(rho : ℂ),
        Finset.mem_toList.mpr hmembership,
        sub_self (rho : ℂ)⟩)

/-- Every scaled target atomic term vanishes at a nearby nontarget completed
zero. -/
theorem completedZeroScaledGaussianAtomicTerm_eq_zero_of_near_of_ne
    (coefficient : ZetaCompletedZeroCoordinate → ℂ)
    (target rho : ZetaCompletedZeroCoordinate)
    (scale : ℝ)
    (hnear : |(rho : ℂ).im - (target : ℂ).im| ≤ 2)
    (hne : rho ≠ target) :
    completedZeroScaledGaussianAtomicTerm coefficient target scale rho = 0 := by
  have hmultiplierZero :
      completedZeroTargetGaussianMultiplier target rho = 0 :=
    completedZeroTargetGaussianMultiplier_eq_zero_of_near_of_ne
      target rho hnear hne
  exact Eq.trans
    (congrArg
      (fun value : ℂ =>
        coefficient rho * value *
          fullGaussianLaplaceKernel
            ((scale : ℂ) * ((rho : ℂ) - (target : ℂ))))
      hmultiplierZero)
    (Eq.trans
      (congrArg
        (fun value : ℂ =>
          value *
            fullGaussianLaplaceKernel
              ((scale : ℂ) * ((rho : ℂ) - (target : ℂ))))
        (mul_zero (coefficient rho)))
      (zero_mul
        (fullGaussianLaplaceKernel
          ((scale : ℂ) * ((rho : ℂ) - (target : ℂ))))))

theorem completedZeroScaledGaussianAtomicTerm_eq_combined_mul_kernel
    (coefficient : ZetaCompletedZeroCoordinate → ℂ)
    (target rho : ZetaCompletedZeroCoordinate)
    (scale : ℝ) :
    completedZeroScaledGaussianAtomicTerm coefficient target scale rho =
      (coefficient rho *
        completedZeroTargetGaussianMultiplier target rho) *
      fullGaussianLaplaceKernel
        ((scale : ℂ) * ((rho : ℂ) - (target : ℂ))) := by
  have hdefinition :
      completedZeroScaledGaussianAtomicTerm coefficient target scale rho =
        coefficient rho *
          completedZeroTargetGaussianMultiplier target rho *
          fullGaussianLaplaceKernel
            ((scale : ℂ) * ((rho : ℂ) - (target : ℂ))) :=
    rfl
  exact Eq.trans hdefinition
    (Eq.refl
      ((coefficient rho *
        completedZeroTargetGaussianMultiplier target rho) *
        fullGaussianLaplaceKernel
          ((scale : ℂ) * ((rho : ℂ) - (target : ℂ)))))

theorem completedZeroScaledGaussianAtomicTerm_function_eq
    (coefficient : ZetaCompletedZeroCoordinate → ℂ)
    (target : ZetaCompletedZeroCoordinate)
    (scale : ℝ) :
    completedZeroScaledGaussianAtomicTerm coefficient target scale =
      fun rho : ZetaCompletedZeroCoordinate =>
        (coefficient rho *
          completedZeroTargetGaussianMultiplier target rho) *
        fullGaussianLaplaceKernel
          ((scale : ℂ) * ((rho : ℂ) - (target : ℂ))) := by
  funext rho
  exact completedZeroScaledGaussianAtomicTerm_eq_combined_mul_kernel
    coefficient target rho scale

/-- Polynomial coefficient growth and completed-zero counting make every
positive-scale full-Gaussian atomic family absolutely summable. -/
theorem summable_completedZeroScaledGaussianAtomicTerm
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
    Summable
      (completedZeroScaledGaussianAtomicTerm coefficient target scale) := by
  have hmultiplierGrowth :
      CompletedZeroAtomicPolynomialGrowth
        (fun rho : ZetaCompletedZeroCoordinate =>
          completedZeroTargetGaussianMultiplier target rho) :=
    finiteSpectralZeroMultiplier_polynomialGrowth
      (completedZeroTargetExceptionalValues target 2 zero_le_two)
  have hcombinedGrowth :
      CompletedZeroAtomicPolynomialGrowth
        (fun rho : ZetaCompletedZeroCoordinate =>
          coefficient rho *
            completedZeroTargetGaussianMultiplier target rho) :=
    CompletedZeroAtomicPolynomialGrowth.mul
      coefficient
      (fun rho : ZetaCompletedZeroCoordinate =>
        completedZeroTargetGaussianMultiplier target rho)
      hgrowth
      hmultiplierGrowth
  have hkernelDecay :
      ∀ degree : ℕ,
        ∃ bound : ℝ,
          0 < bound ∧
          ∀ rho : ZetaCompletedZeroCoordinate,
            ‖fullGaussianLaplaceKernel
              ((scale : ℂ) * ((rho : ℂ) - (target : ℂ)))‖ ≤
                bound *
                  zetaCompletedZeroCenteredHeight rho ^
                    (-(degree : ℤ)) :=
    fun degree =>
      exists_fullGaussianLaplaceKernel_scaled_shift_decay
        target scale hscale degree
  exact Eq.mpr
    (congrArg Summable
      (completedZeroScaledGaussianAtomicTerm_function_eq
        coefficient target scale))
    (CompletedZeroAtomicPolynomialGrowth.summable_mul_of_rapidDecay
      hbranch hpartialOneTwo hcompactOneTwo hfinite
      hpartialLeft hcompactBoundary
      (fun rho : ZetaCompletedZeroCoordinate =>
        coefficient rho *
          completedZeroTargetGaussianMultiplier target rho)
      (fun rho : ZetaCompletedZeroCoordinate =>
        fullGaussianLaplaceKernel
          ((scale : ℂ) * ((rho : ℂ) - (target : ℂ))))
      hcombinedGrowth
      hkernelDecay)

end ZetaAdmissibleFunction
end
end LFunctions
end Boundary
