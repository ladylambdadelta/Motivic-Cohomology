import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaZeroTail.ZetaZeroMultiplicitySummability.ZetaZeroMultiplicityCounting.ZetaCompletedZeroJensen.ZetaEntireJensen.EntireJensenFormula.ZeroFreePrimitive.AnalyticLogBranch.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaZeroTail.ZetaZeroMultiplicitySummability.ZetaZeroMultiplicityCounting.ZetaCompletedZeroJensen.ZetaEntireJensen.EntireJensenFormula.ZeroFreePrimitive.CauchyMean.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaZeroTail.ZetaZeroMultiplicitySummability.ZetaZeroMultiplicityCounting.ZetaCompletedZeroJensen.ZetaEntireJensen.EntireJensenFormula.FiniteZeroProduct.Owner

/-!
# Zero-free quotient boundary mean for Jensen formula

This file owns the zero-free quotient boundary logarithm comparison used by
the boundary-log assembly layer.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped Topology

theorem entireFunction_zeroFreeOnClosedDisk_boundaryLogAverage_eq_origin_log_norm_ownerRoot
    (Q : ℂ → ℂ)
    (ρ : ℝ)
    (hρ : 1 ≤ ρ)
    (hQ_an : ∀ w : ℂ, ‖w‖ ≤ ρ → AnalyticAt ℂ Q w)
    (hzero : ∀ w : ℂ, ‖w‖ ≤ ρ → Q w ≠ 0) :
    (2 * Real.pi)⁻¹ *
        (∫ θ in (0 : ℝ)..(2 * Real.pi),
          Real.log ‖Q ((ρ : ℂ) * Complex.exp (θ * Complex.I))‖) =
      Real.log ‖Q 0‖ := by
  let branch :=
    entireFunction_zeroFreeOnClosedDisk_exists_analyticLogBranch_from_simplyConnectedDisk
      Q hρ hQ_an hzero
  match branch with
  | ⟨L, hL_an, hL_log⟩ =>
      have hboundary :
          (2 * Real.pi)⁻¹ *
              (∫ θ in (0 : ℝ)..(2 * Real.pi),
                Real.log ‖Q ((ρ : ℂ) * Complex.exp (θ * Complex.I))‖) =
            (2 * Real.pi)⁻¹ *
              (∫ θ in (0 : ℝ)..(2 * Real.pi),
                (L ((ρ : ℂ) * Complex.exp (θ * Complex.I))).re) := by
        exact congrArg
          (fun x : ℝ => (2 * Real.pi)⁻¹ * x)
          (by
            apply intervalIntegral.integral_congr
            intro θ hθ
            have hcircle_norm :
                ‖((ρ : ℂ) * Complex.exp (θ * Complex.I))‖ ≤ ρ := by
              have hρ_nonneg : 0 ≤ ρ :=
                le_trans zero_le_one hρ
              have hnorm_eq : ‖((ρ : ℂ) * Complex.exp (θ * Complex.I))‖ = ρ := by
                calc
                  ‖((ρ : ℂ) * Complex.exp (θ * Complex.I))‖ =
                      ‖(ρ : ℂ)‖ * ‖Complex.exp (θ * Complex.I)‖ := by
                    exact norm_mul (ρ : ℂ) (Complex.exp (θ * Complex.I))
                  _ = ρ * ‖Complex.exp (θ * Complex.I)‖ := by
                    exact congrArg
                      (fun x : ℝ => x * ‖Complex.exp (θ * Complex.I)‖)
                      ((RCLike.norm_ofReal ρ).trans (abs_of_nonneg hρ_nonneg))
                  _ = ρ * 1 := by
                    exact congrArg (fun x : ℝ => ρ * x)
                      (Complex.norm_exp_ofReal_mul_I θ)
                  _ = ρ := by
                    exact mul_one ρ
              exact le_of_eq hnorm_eq
            exact
              (entireFunction_analyticLogBranch_re_eq_log_norm
                Q L hcircle_norm hL_log).symm)
      have hmean :
          (2 * Real.pi)⁻¹ *
              (∫ θ in (0 : ℝ)..(2 * Real.pi),
                (L ((ρ : ℂ) * Complex.exp (θ * Complex.I))).re) =
            (L 0).re :=
        entireFunction_analyticLog_re_holomorphicMeanValue_circle
          L hρ hL_an
      have hcenter :
          (L 0).re = Real.log ‖Q 0‖ :=
        entireFunction_analyticLogBranch_center_re_eq_log_norm
          Q L hρ hL_log
      calc
        (2 * Real.pi)⁻¹ *
            (∫ θ in (0 : ℝ)..(2 * Real.pi),
              Real.log ‖Q ((ρ : ℂ) * Complex.exp (θ * Complex.I))‖) =
            (2 * Real.pi)⁻¹ *
              (∫ θ in (0 : ℝ)..(2 * Real.pi),
                (L ((ρ : ℂ) * Complex.exp (θ * Complex.I))).re) :=
          hboundary
        _ = (L 0).re := hmean
        _ = Real.log ‖Q 0‖ := hcenter

/-- Origin normalization for any removable quotient whose closed-disk
factorization is normalized by the finite product. -/
theorem entireFunction_standardJensenFormula_nonzeroAtOrigin_supportFiniteRemovableQuotient_origin_log_norm_ownerRoot
    (F Q : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hF0 : F 0 ≠ 0)
    (ρ : ℝ)
    (hρ : 1 ≤ ρ)
    (hfactor :
      ∀ w : ℂ,
        ‖w‖ ≤ ρ →
        F w =
          Q w *
            entireFunction_standardJensenFormula_nonzeroAtOrigin_supportFiniteZeroDivisorProduct
              F hF hF0 ρ w) :
    Real.log ‖Q 0‖ = Real.log ‖F 0‖ := by
  have hρ_nonneg : 0 ≤ ρ :=
    le_trans zero_le_one hρ
  have hρ_origin : ‖(0 : ℂ)‖ ≤ ρ := by
    exact
      Eq.subst
        (motive := fun x : ℝ => x ≤ ρ)
        (norm_zero : ‖(0 : ℂ)‖ = 0).symm
        hρ_nonneg
  have hfactor_origin :
      F 0 =
        Q 0 *
          entireFunction_standardJensenFormula_nonzeroAtOrigin_supportFiniteZeroDivisorProduct
            F hF hF0 ρ 0 :=
    hfactor 0 hρ_origin
  have hproduct_origin :
      entireFunction_standardJensenFormula_nonzeroAtOrigin_supportFiniteZeroDivisorProduct
          F hF hF0 ρ 0 = 1 :=
    entireFunction_standardJensenFormula_nonzeroAtOrigin_supportFiniteZeroDivisorProduct_origin
      F hF hF0 ρ
  have hQ_origin : Q 0 = F 0 := by
    calc
      Q 0 = Q 0 * 1 :=
        (mul_one (Q 0)).symm
      _ =
          Q 0 *
            entireFunction_standardJensenFormula_nonzeroAtOrigin_supportFiniteZeroDivisorProduct
              F hF hF0 ρ 0 :=
        congrArg (fun x : ℂ => Q 0 * x) hproduct_origin.symm
      _ = F 0 :=
        hfactor_origin.symm
  exact congrArg (fun x : ℝ => Real.log x) (congrArg norm hQ_origin)

end
end LFunctions
end Boundary
