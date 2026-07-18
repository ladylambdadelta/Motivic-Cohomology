import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaZeroTail.WeightedTail.KernelDensity.AtomicDistributionExceptionalWindow
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaZeroTail.WeightedTail.KernelDensity.AtomicDistributionGrowth
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaZeroTail.WeightedTail.KernelDensity.AtomicDistributionGaussianProbe
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaZeroTail.WeightedTail.KernelDensity.AtomicDistributionGaussianCompletion
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform

/-!
# Gaussian localization of one completed-zero atom

For a selected completed zero, first apply the finite targeted exceptional
operator to remove all nearby nontarget zeros.  A Gaussian Laplace kernel
centered at the target then has a nonzero target value and exponentially
suppresses the remaining ordinate-separated tail.  Polynomial coefficient
growth and Jensen counting justify dominated passage to the Gaussian limit.
-/

namespace Boundary
namespace LFunctions
noncomputable section
namespace ZetaAdmissibleFunction

/-- The admissible targeted Gaussian cutoff after the finite nearby nontarget
zeros have been removed. -/
noncomputable def completedZeroTargetGaussianCutoffProbe
    (target : ZetaCompletedZeroCoordinate)
    (exceptionalRadius cutoffRadius : ℝ)
    (hexceptionalRadius : 0 ≤ exceptionalRadius)
    (hcutoffRadius : 0 < cutoffRadius) : ZetaAdmissibleFunction :=
  finiteSpectralZeroOperator
    (completedZeroTargetExceptionalValues
      target exceptionalRadius hexceptionalRadius)
    (complexExponentialModulate (target : ℂ)
      (admissibleGaussianCutoff cutoffRadius hcutoffRadius))

/-- Global atomic annihilation gives an exact zero identity on every targeted
compact Gaussian cutoff. -/
theorem completedZeroAtomic_targetGaussianCutoff_tsum_eq_zero
    (coefficient : ZetaCompletedZeroCoordinate → ℂ)
    (hvanishing :
      ∀ f : ZetaAdmissibleFunction,
        (∑' rho : ZetaCompletedZeroCoordinate,
          coefficient rho * zetaSpectralEval f (rho : ℂ)) = 0)
    (target : ZetaCompletedZeroCoordinate)
    (exceptionalRadius cutoffRadius : ℝ)
    (hexceptionalRadius : 0 ≤ exceptionalRadius)
    (hcutoffRadius : 0 < cutoffRadius) :
    (∑' rho : ZetaCompletedZeroCoordinate,
      coefficient rho *
        zetaSpectralEval
          (completedZeroTargetGaussianCutoffProbe
            target exceptionalRadius cutoffRadius
            hexceptionalRadius hcutoffRadius)
          (rho : ℂ)) = 0 :=
  hvanishing
    (completedZeroTargetGaussianCutoffProbe
      target exceptionalRadius cutoffRadius
      hexceptionalRadius hcutoffRadius)

/-- The targeted Gaussian cutoff evaluation factors into the finite exceptional
multiplier and the centered compact-Gaussian transform. -/
theorem zetaSpectralEval_completedZeroTargetGaussianCutoffProbe
    (target rho : ZetaCompletedZeroCoordinate)
    (exceptionalRadius cutoffRadius : ℝ)
    (hexceptionalRadius : 0 ≤ exceptionalRadius)
    (hcutoffRadius : 0 < cutoffRadius) :
    zetaSpectralEval
        (completedZeroTargetGaussianCutoffProbe
          target exceptionalRadius cutoffRadius
          hexceptionalRadius hcutoffRadius)
        (rho : ℂ) =
      ((completedZeroTargetExceptionalValues
          target exceptionalRadius hexceptionalRadius).toList.map
        (fun sample : ℂ => sample - (rho : ℂ))).prod *
        zetaSpectralEval
          (admissibleGaussianCutoff cutoffRadius hcutoffRadius)
          ((rho : ℂ) - (target : ℂ)) := by
  have hoperator := zetaSpectralEval_finiteSpectralZeroOperator
    (completedZeroTargetExceptionalValues
      target exceptionalRadius hexceptionalRadius)
    (complexExponentialModulate (target : ℂ)
      (admissibleGaussianCutoff cutoffRadius hcutoffRadius))
    (rho : ℂ)
  have hmodulation := zetaSpectralEval_complexExponentialModulate
    (target : ℂ)
    (rho : ℂ)
    (admissibleGaussianCutoff cutoffRadius hcutoffRadius)
  exact Eq.trans hoperator
    (congrArg
      (fun value : ℂ =>
        ((completedZeroTargetExceptionalValues
          target exceptionalRadius hexceptionalRadius).toList.map
            (fun sample : ℂ => sample - (rho : ℂ))).prod * value)
      hmodulation)

/-- At the selected target, the centered compact-Gaussian transform is
evaluated at zero and the finite multiplier is nonzero. -/
theorem zetaSpectralEval_completedZeroTargetGaussianCutoffProbe_target
    (target : ZetaCompletedZeroCoordinate)
    (exceptionalRadius cutoffRadius : ℝ)
    (hexceptionalRadius : 0 ≤ exceptionalRadius)
    (hcutoffRadius : 0 < cutoffRadius) :
    zetaSpectralEval
        (completedZeroTargetGaussianCutoffProbe
          target exceptionalRadius cutoffRadius
          hexceptionalRadius hcutoffRadius)
        (target : ℂ) =
      ((completedZeroTargetExceptionalValues
          target exceptionalRadius hexceptionalRadius).toList.map
        (fun sample : ℂ => sample - (target : ℂ))).prod *
        zetaSpectralEval
          (admissibleGaussianCutoff cutoffRadius hcutoffRadius) 0 := by
  have hfactor :=
    zetaSpectralEval_completedZeroTargetGaussianCutoffProbe
      target target exceptionalRadius cutoffRadius
      hexceptionalRadius hcutoffRadius
  have hdifference : (target : ℂ) - (target : ℂ) = 0 :=
    sub_self (target : ℂ)
  exact Eq.trans hfactor
    (congrArg
      (fun value : ℂ =>
        ((completedZeroTargetExceptionalValues
          target exceptionalRadius hexceptionalRadius).toList.map
            (fun sample : ℂ => sample - (target : ℂ))).prod *
          zetaSpectralEval
            (admissibleGaussianCutoff cutoffRadius hcutoffRadius) value)
      hdifference)

/-- Targeted Gaussian localization extracts one coefficient from a vanishing
polynomial-growth completed-zero atomic Laplace distribution. -/
theorem completedZeroAtomicLaplaceDistribution_coefficient_eq_zero_at
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
          coefficient rho * zetaSpectralEval f (rho : ℂ)) = 0)
    (target : ZetaCompletedZeroCoordinate) :
    coefficient target = 0 := by
  let targetMultiplier : ℂ :=
    completedZeroTargetGaussianMultiplier target target
  let targetValue : ℂ :=
    coefficient target * targetMultiplier * fullGaussianLaplaceKernel 0
  have htargetMultiplierNonzero : targetMultiplier ≠ 0 :=
    completedZeroTargetExceptionalMultiplier_ne_zero
      target 2 zero_le_two
  have htargetKernelNonzero : fullGaussianLaplaceKernel 0 ≠ 0 :=
    fullGaussianLaplaceKernel_zero_ne_zero
  have hscalePositive :
      ∀ n : ℕ, 0 < (n : ℝ) + 1 :=
    fun n => add_pos_of_nonneg_of_pos (Nat.cast_nonneg n) zero_lt_one
  have hsummableScaled :
      ∀ n : ℕ,
        Summable
          (completedZeroScaledGaussianAtomicTerm
            coefficient target ((n : ℝ) + 1)) :=
    fun n =>
      summable_completedZeroScaledGaussianAtomicTerm
        hbranch hpartialOneTwo hcompactOneTwo hfinite
        hpartialLeft hcompactBoundary coefficient hgrowth target
        ((n : ℝ) + 1) (hscalePositive n)
  have hscaledZero :
      ∀ n : ℕ,
        (∑' rho : ZetaCompletedZeroCoordinate,
          completedZeroScaledGaussianAtomicTerm
            coefficient target ((n : ℝ) + 1) rho) = 0 :=
    fun n =>
      completedZeroAtomic_scaledFullGaussian_tsum_eq_zero
        hbranch hpartialOneTwo hcompactOneTwo hfinite
        hpartialLeft hcompactBoundary coefficient hgrowth
        hsummable hvanishing target ((n : ℝ) + 1) (hscalePositive n)
  have htargetTerm :
      ∀ n : ℕ,
        completedZeroScaledGaussianAtomicTerm
            coefficient target ((n : ℝ) + 1) target = targetValue := by
    intro n
    have hdifference : (target : ℂ) - (target : ℂ) = 0 :=
      sub_self (target : ℂ)
    have hscaledDifference :
        ((((n : ℝ) + 1 : ℝ) : ℂ) *
          ((target : ℂ) - (target : ℂ))) = 0 :=
      Eq.trans
        (congrArg
          (fun value : ℂ => ((((n : ℝ) + 1 : ℝ) : ℂ) * value))
          hdifference)
        (mul_zero ((((n : ℝ) + 1 : ℝ) : ℂ)))
    exact congrArg
      (fun value : ℂ =>
        coefficient target * targetMultiplier *
          fullGaussianLaplaceKernel value)
      hscaledDifference
  have hsplit :
      ∀ n : ℕ,
        (∑' rho : ZetaCompletedZeroCoordinate,
          completedZeroScaledGaussianAtomicTerm
            coefficient target ((n : ℝ) + 1) rho) =
          targetValue +
            completedZeroScaledGaussianAtomicTail
              coefficient target ((n : ℝ) + 1) := by
    intro n
    have hraw := tsum_eq_add_tsum_ite
      (hsummableScaled n)
      target
    exact Eq.trans hraw
      (congrArg₂ Add.add
        (htargetTerm n)
        (Eq.refl
          (completedZeroScaledGaussianAtomicTail
            coefficient target ((n : ℝ) + 1))))
  have hconstantPlusTailZero :
      ∀ n : ℕ,
        targetValue +
          completedZeroScaledGaussianAtomicTail
            coefficient target ((n : ℝ) + 1) = 0 :=
    fun n => Eq.trans (hsplit n).symm (hscaledZero n)
  have htailLimit :=
    completedZeroScaledGaussianAtomicTail_tendsto_zero
      hbranch hpartialOneTwo hcompactOneTwo hfinite
      hpartialLeft hcompactBoundary coefficient hgrowth target
  have hleftLimit :
      Filter.Tendsto
        (fun n : ℕ =>
          targetValue +
            completedZeroScaledGaussianAtomicTail
              coefficient target ((n : ℝ) + 1))
        Filter.atTop
        (nhds targetValue) := by
    have hconstantLimit :
        Filter.Tendsto
          (fun n : ℕ => targetValue)
          Filter.atTop
          (nhds targetValue) :=
      tendsto_const_nhds
    have haddLimit :
        Filter.Tendsto
          (fun n : ℕ =>
            targetValue +
              completedZeroScaledGaussianAtomicTail
                coefficient target ((n : ℝ) + 1))
          Filter.atTop
          (nhds (targetValue + 0)) :=
      Filter.Tendsto.add hconstantLimit htailLimit
    exact Eq.mp
      (congrArg
        (fun limit : ℂ =>
          Filter.Tendsto
            (fun n : ℕ =>
              targetValue +
                completedZeroScaledGaussianAtomicTail
                  coefficient target ((n : ℝ) + 1))
            Filter.atTop
            (nhds limit))
        (add_zero targetValue))
      haddLimit
  have hrightLimit :
      Filter.Tendsto
        (fun n : ℕ =>
          targetValue +
            completedZeroScaledGaussianAtomicTail
              coefficient target ((n : ℝ) + 1))
        Filter.atTop
        (nhds 0) :=
    Filter.Tendsto.congr'
      (Filter.Eventually.of_forall
        (fun n => (hconstantPlusTailZero n).symm))
      tendsto_const_nhds
  have htargetValueZero : targetValue = 0 :=
    tendsto_nhds_unique hleftLimit hrightLimit
  have htargetValueAssociated :
      targetValue =
        coefficient target *
          (targetMultiplier * fullGaussianLaplaceKernel 0) :=
    mul_assoc
      (coefficient target)
      targetMultiplier
      (fullGaussianLaplaceKernel 0)
  have hassociatedZero :
      coefficient target *
        (targetMultiplier * fullGaussianLaplaceKernel 0) = 0 :=
    Eq.mp
      (congrArg
        (fun value : ℂ => value = 0)
        htargetValueAssociated)
      htargetValueZero
  have hcoefficientOrProductZero :
      coefficient target = 0 ∨
        targetMultiplier * fullGaussianLaplaceKernel 0 = 0 :=
    mul_eq_zero.mp hassociatedZero
  exact Or.elim hcoefficientOrProductZero
    (fun hcoefficientZero => hcoefficientZero)
    (fun hproductZero =>
      False.elim
        ((mul_ne_zero htargetMultiplierNonzero htargetKernelNonzero)
          hproductZero))

end ZetaAdmissibleFunction
end
end LFunctions
end Boundary
