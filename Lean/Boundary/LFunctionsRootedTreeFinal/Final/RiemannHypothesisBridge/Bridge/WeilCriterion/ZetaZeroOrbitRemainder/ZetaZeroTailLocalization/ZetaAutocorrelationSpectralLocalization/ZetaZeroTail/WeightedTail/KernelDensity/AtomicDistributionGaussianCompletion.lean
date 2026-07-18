import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaZeroTail.WeightedTail.KernelDensity.AtomicDistributionGaussianCutoffCompletion
import Mathlib.Analysis.Normed.Group.Tannery

/-!
# Gaussian completion of completed-zero atomic distributions

The finite exceptional multiplier removes every nontarget zero in the closed
ordinate window of radius two.  The compact Gaussian probes then converge in
the polynomially weighted completed-zero evaluation norm to the full scaled
Gaussian kernel.  This file owns that completion and its separated-tail limit.
-/

namespace Boundary
namespace LFunctions
noncomputable section
namespace ZetaAdmissibleFunction

theorem completedZeroNaturalScale_cast_eq
    (n : ℕ) :
    ((((n : ℝ) + 1 : ℝ) : ℂ)) = ((n : ℝ) : ℂ) + 1 := by
  exact map_add (algebraMap ℝ ℂ) (n : ℝ) 1

theorem completedZeroNaturalScaleGaussian_eq_scaledKernel
    (target rho : ZetaCompletedZeroCoordinate)
    (n : ℕ) :
    fullGaussianLaplaceKernel
        (((((n : ℝ) + 1 : ℝ) : ℂ)) *
          ((rho : ℂ) - (target : ℂ))) =
      completedZeroNaturalScaleGaussian target rho n := by
  exact congrArg
    (fun scale : ℂ =>
      fullGaussianLaplaceKernel
        (scale * ((rho : ℂ) - (target : ℂ))))
    (completedZeroNaturalScale_cast_eq n)

theorem completedZeroScaledGaussianAtomicTerm_natScale_eq
    (coefficient : ZetaCompletedZeroCoordinate → ℂ)
    (target rho : ZetaCompletedZeroCoordinate)
    (n : ℕ) :
    completedZeroScaledGaussianAtomicTerm
        coefficient target ((n : ℝ) + 1) rho =
      (coefficient rho * completedZeroTargetGaussianMultiplier target rho) *
        completedZeroNaturalScaleGaussian target rho n := by
  exact Eq.trans
    (completedZeroScaledGaussianAtomicTerm_eq_combined_mul_kernel
      coefficient target rho ((n : ℝ) + 1))
    (congrArg
      (fun kernel : ℂ =>
        (coefficient rho *
          completedZeroTargetGaussianMultiplier target rho) * kernel)
      (completedZeroNaturalScaleGaussian_eq_scaledKernel target rho n))

theorem completedZeroScaledGaussianAtomicTerm_natScale_function_eq
    (coefficient : ZetaCompletedZeroCoordinate → ℂ)
    (target rho : ZetaCompletedZeroCoordinate) :
    (fun n : ℕ =>
      completedZeroScaledGaussianAtomicTerm
        coefficient target ((n : ℝ) + 1) rho) =
      fun n : ℕ =>
        (coefficient rho * completedZeroTargetGaussianMultiplier target rho) *
          completedZeroNaturalScaleGaussian target rho n := by
  funext n
  exact completedZeroScaledGaussianAtomicTerm_natScale_eq
    coefficient target rho n

/-- An atomic functional vanishing on all compact admissible probes also
vanishes on every positive-scale full Gaussian after the radius-two finite
exceptional operator. -/
theorem completedZeroAtomic_scaledFullGaussian_tsum_eq_zero
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
    (target : ZetaCompletedZeroCoordinate)
    (scale : ℝ)
    (hscale : 0 < scale) :
    (∑' rho : ZetaCompletedZeroCoordinate,
      completedZeroScaledGaussianAtomicTerm
        coefficient target scale rho) = 0 := by
  let compactSum : ℕ → ℂ :=
    fun n : ℕ =>
      ∑' rho : ZetaCompletedZeroCoordinate,
        coefficient rho *
          zetaSpectralEval
            (completedZeroTargetScaledGaussianCutoffProbe
              target scale n)
            (rho : ℂ)
  have hcompactZero : ∀ n : ℕ, compactSum n = 0 :=
    fun n =>
      hvanishing
        (completedZeroTargetScaledGaussianCutoffProbe
          target scale n)
  have hcompactLimitZero :
      Filter.Tendsto compactSum Filter.atTop (nhds 0) :=
    Filter.Tendsto.congr'
      (Filter.Eventually.of_forall (fun n => (hcompactZero n).symm))
      tendsto_const_nhds
  have hcompactLimitFull :=
    completedZeroAtomic_targetScaledGaussianCutoff_tsum_tendsto_full
      hbranch hpartialOneTwo hcompactOneTwo hfinite
      hpartialLeft hcompactBoundary coefficient hgrowth
      target scale hscale
  exact tendsto_nhds_unique hcompactLimitFull hcompactLimitZero

/-- A separated completed-zero atomic Gaussian term tends to zero along natural
scales. -/
theorem completedZeroScaledGaussianAtomicTerm_natScale_tendsto_zero_of_separated
    (coefficient : ZetaCompletedZeroCoordinate → ℂ)
    (target rho : ZetaCompletedZeroCoordinate)
    (hseparated : 2 ≤ |(rho : ℂ).im - (target : ℂ).im|) :
    Filter.Tendsto
      (fun n : ℕ =>
        completedZeroScaledGaussianAtomicTerm
          coefficient target ((n : ℝ) + 1) rho)
      Filter.atTop
      (nhds 0) := by
  have hkernelLimit :=
    fullGaussianLaplaceKernel_natScale_shift_tendsto_zero
      target rho hseparated
  have hconstantLimit :
      Filter.Tendsto
        (fun n : ℕ =>
          coefficient rho *
            completedZeroTargetGaussianMultiplier target rho)
        Filter.atTop
        (nhds
          (coefficient rho *
            completedZeroTargetGaussianMultiplier target rho)) :=
    tendsto_const_nhds
  have hproductLimit :=
    Filter.Tendsto.mul hconstantLimit hkernelLimit
  have hproductZeroLimit :
      Filter.Tendsto
        (fun n : ℕ =>
          (coefficient rho *
            completedZeroTargetGaussianMultiplier target rho) *
            completedZeroNaturalScaleGaussian target rho n)
        Filter.atTop
        (nhds 0) :=
    Eq.mp
      (congrArg
        (fun limit : ℂ =>
          Filter.Tendsto
            (fun n : ℕ =>
              (coefficient rho *
                completedZeroTargetGaussianMultiplier target rho) *
                completedZeroNaturalScaleGaussian target rho n)
            Filter.atTop
            (nhds limit))
        (mul_zero
          (coefficient rho *
            completedZeroTargetGaussianMultiplier target rho)))
      hproductLimit
  exact Eq.mpr
    (congrArg
      (fun function : ℕ → ℂ =>
        Filter.Tendsto function Filter.atTop (nhds 0))
      (completedZeroScaledGaussianAtomicTerm_natScale_function_eq
        coefficient target rho))
    hproductZeroLimit

/-- A separated natural-scale atomic Gaussian term is norm-dominated by its
scale-one term. -/
theorem completedZeroScaledGaussianAtomicTerm_natScale_norm_le_oneScale_of_separated
    (coefficient : ZetaCompletedZeroCoordinate → ℂ)
    (target rho : ZetaCompletedZeroCoordinate)
    (hseparated : 2 ≤ |(rho : ℂ).im - (target : ℂ).im|)
    (n : ℕ) :
    ‖completedZeroScaledGaussianAtomicTerm
        coefficient target ((n : ℝ) + 1) rho‖ ≤
      ‖completedZeroScaledGaussianAtomicTerm coefficient target 1 rho‖ := by
  have hkernelBound :=
    fullGaussianLaplaceKernel_natScale_shift_norm_le_oneScale
      target rho hseparated n
  have hcoefficientMultiplierNonnegative :
      0 ≤ ‖coefficient rho *
        completedZeroTargetGaussianMultiplier target rho‖ :=
    norm_nonneg
      (coefficient rho *
        completedZeroTargetGaussianMultiplier target rho)
  have hscaledKernelBound :=
    mul_le_mul_of_nonneg_left hkernelBound
      hcoefficientMultiplierNonnegative
  have hleft :
      ‖completedZeroScaledGaussianAtomicTerm
          coefficient target ((n : ℝ) + 1) rho‖ =
        ‖coefficient rho *
          completedZeroTargetGaussianMultiplier target rho‖ *
          ‖completedZeroNaturalScaleGaussian target rho n‖ :=
    Eq.trans
      (congrArg Norm.norm
        (completedZeroScaledGaussianAtomicTerm_natScale_eq
          coefficient target rho n))
      (norm_mul
        (coefficient rho *
          completedZeroTargetGaussianMultiplier target rho)
        (completedZeroNaturalScaleGaussian target rho n))
  have hright :
      ‖completedZeroScaledGaussianAtomicTerm coefficient target 1 rho‖ =
        ‖coefficient rho *
          completedZeroTargetGaussianMultiplier target rho‖ *
          completedZeroScaledGaussianNorm target rho 1 :=
    norm_mul
      (coefficient rho *
        completedZeroTargetGaussianMultiplier target rho)
      (fullGaussianLaplaceKernel
        ((1 : ℂ) * ((rho : ℂ) - (target : ℂ))))
  have hproposition := congrArg₂ LE.le hleft.symm hright.symm
  exact Eq.mp hproposition hscaledKernelBound

/-- Along natural scales, the full-Gaussian nontarget tail tends to zero after
the radius-two exceptional window has been removed. -/
theorem completedZeroScaledGaussianAtomicTail_tendsto_zero
    (hbranch : Complex.BinetSecondFormulaBranchUniformTailAbsorption)
    (hpartialOneTwo : BoundaryLineOneAbelPartialMajorant)
    (hcompactOneTwo : PoleClearedOneTwoStripCompactBoundaryBound)
    (hfinite : PoleClearedRightCriticalStripAdmissibleGrowth)
    (hpartialLeft : ReflectedBoundaryAbelPartialMajorant)
    (hcompactBoundary : PoleClearedRightCriticalStripCompactBoundaryBound)
    (coefficient : ZetaCompletedZeroCoordinate → ℂ)
    (hgrowth : CompletedZeroAtomicPolynomialGrowth coefficient)
    (target : ZetaCompletedZeroCoordinate) :
    Filter.Tendsto
      (fun n : ℕ =>
        completedZeroScaledGaussianAtomicTail
          coefficient target ((n : ℝ) + 1))
      Filter.atTop
      (nhds 0) := by
  let term : ℕ → ZetaCompletedZeroCoordinate → ℂ :=
    fun n rho =>
      if rho = target then 0
      else completedZeroScaledGaussianAtomicTerm
        coefficient target ((n : ℝ) + 1) rho
  let bound : ZetaCompletedZeroCoordinate → ℝ :=
    fun rho =>
      ‖completedZeroScaledGaussianAtomicTerm coefficient target 1 rho‖
  have hscaleOnePositive : (0 : ℝ) < 1 := zero_lt_one
  have hscaleOneSummable :
      Summable
        (completedZeroScaledGaussianAtomicTerm coefficient target 1) :=
    summable_completedZeroScaledGaussianAtomicTerm
      hbranch hpartialOneTwo hcompactOneTwo hfinite
      hpartialLeft hcompactBoundary coefficient hgrowth target
      1 hscaleOnePositive
  have hboundSummable : Summable bound :=
    hscaleOneSummable.norm
  have hpointwise :
      ∀ rho : ZetaCompletedZeroCoordinate,
        Filter.Tendsto
          (fun n : ℕ => term n rho)
          Filter.atTop
          (nhds 0) := by
    intro rho
    by_cases hrhoTarget : rho = target
    · have htermZero :
          (fun n : ℕ => term n rho) = fun n : ℕ => (0 : ℂ) := by
        funext n
        exact if_pos hrhoTarget
      exact Eq.mpr
        (congrArg
          (fun function : ℕ → ℂ =>
            Filter.Tendsto function Filter.atTop (nhds 0))
          htermZero)
        tendsto_const_nhds
    · by_cases hnear :
        |(rho : ℂ).im - (target : ℂ).im| ≤ 2
      · have htermZero :
            (fun n : ℕ => term n rho) = fun n : ℕ => (0 : ℂ) := by
          funext n
          have hif : term n rho =
              completedZeroScaledGaussianAtomicTerm
                coefficient target ((n : ℝ) + 1) rho :=
            if_neg hrhoTarget
          have hatomicZero :
              completedZeroScaledGaussianAtomicTerm
                coefficient target ((n : ℝ) + 1) rho = 0 :=
            completedZeroScaledGaussianAtomicTerm_eq_zero_of_near_of_ne
              coefficient target rho ((n : ℝ) + 1) hnear hrhoTarget
          exact Eq.trans hif hatomicZero
        exact Eq.mpr
          (congrArg
            (fun function : ℕ → ℂ =>
              Filter.Tendsto function Filter.atTop (nhds 0))
            htermZero)
          tendsto_const_nhds
      · have hseparated :
          2 ≤ |(rho : ℂ).im - (target : ℂ).im| :=
          le_of_not_ge hnear
        have hatomicLimit :
            Filter.Tendsto
              (fun n : ℕ =>
                completedZeroScaledGaussianAtomicTerm
                  coefficient target ((n : ℝ) + 1) rho)
              Filter.atTop
              (nhds 0) :=
          completedZeroScaledGaussianAtomicTerm_natScale_tendsto_zero_of_separated
            coefficient target rho hseparated
        exact Filter.Tendsto.congr'
          (Filter.Eventually.of_forall
            (fun n => (if_neg hrhoTarget).symm))
          hatomicLimit
  have hdomination :
      ∀ᶠ n : ℕ in Filter.atTop,
        ∀ rho : ZetaCompletedZeroCoordinate,
          ‖term n rho‖ ≤ bound rho :=
    Filter.Eventually.of_forall
      (fun n rho => by
        by_cases hrhoTarget : rho = target
        · have hzero : term n rho = 0 := if_pos hrhoTarget
          exact Eq.subst
            (motive := fun value : ℂ => ‖value‖ ≤ bound rho)
            hzero.symm
            (le_trans (Eq.le norm_zero) (norm_nonneg
              (completedZeroScaledGaussianAtomicTerm
                coefficient target 1 rho)))
        · by_cases hnear :
            |(rho : ℂ).im - (target : ℂ).im| ≤ 2
          · have htermZero : term n rho = 0 :=
              Eq.trans (if_neg hrhoTarget)
                (completedZeroScaledGaussianAtomicTerm_eq_zero_of_near_of_ne
                  coefficient target rho ((n : ℝ) + 1) hnear hrhoTarget)
            exact Eq.subst
              (motive := fun value : ℂ => ‖value‖ ≤ bound rho)
              htermZero.symm
              (le_trans (Eq.le norm_zero) (norm_nonneg
                (completedZeroScaledGaussianAtomicTerm
                  coefficient target 1 rho)))
          · have hseparated :
                2 ≤ |(rho : ℂ).im - (target : ℂ).im| :=
              le_of_not_ge hnear
            have hatomicBound :=
              completedZeroScaledGaussianAtomicTerm_natScale_norm_le_oneScale_of_separated
                coefficient target rho hseparated n
            have htermNorm :
                ‖term n rho‖ =
                  ‖completedZeroScaledGaussianAtomicTerm
                    coefficient target ((n : ℝ) + 1) rho‖ :=
              congrArg Norm.norm (if_neg hrhoTarget)
            exact Eq.mp
              (congrArg
                (fun left : ℝ =>
                  left ≤
                    ‖completedZeroScaledGaussianAtomicTerm
                      coefficient target 1 rho‖)
                htermNorm.symm)
              hatomicBound)
  have htannery := tendsto_tsum_of_dominated_convergence
    hboundSummable
    hpointwise
    hdomination
  have hzeroTsum :
      (∑' rho : ZetaCompletedZeroCoordinate, (0 : ℂ)) = 0 :=
    tsum_zero
  exact Eq.mp
    (congrArg
      (fun value : ℂ =>
        Filter.Tendsto
          (fun n : ℕ =>
            completedZeroScaledGaussianAtomicTail
              coefficient target ((n : ℝ) + 1))
          Filter.atTop
          (nhds value))
      hzeroTsum)
    htannery

end ZetaAdmissibleFunction
end
end LFunctions
end Boundary
