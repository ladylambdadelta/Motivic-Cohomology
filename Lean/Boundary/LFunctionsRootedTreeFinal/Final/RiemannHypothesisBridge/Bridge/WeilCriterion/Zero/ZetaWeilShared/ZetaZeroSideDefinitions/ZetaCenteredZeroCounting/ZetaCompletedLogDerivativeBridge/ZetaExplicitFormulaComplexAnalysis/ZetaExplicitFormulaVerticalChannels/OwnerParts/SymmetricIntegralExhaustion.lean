import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.AffineVerticalKernels

/-!
# Symmetric interval exhaustion

This file owns the measure-theoretic passage from a whole-line integrable
kernel to its symmetric truncations over `[-T, T]`.  The channel-specific files
own the integrability and value computations for their kernels.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open Complex
open Filter
open LSeries ArithmeticFunction
open MeasureTheory
open scoped ArithmeticFunction
open scoped Topology

namespace ZetaAdmissibleFunction

/-- Symmetric real intervals exhaust the whole-line integral of an integrable
complex-valued kernel. -/
theorem explicitFormulaSymmetricIntervalIntegral_tendsto_integral
    (φ : ℝ → ℂ) (hφ : Integrable φ (volume : Measure ℝ)) :
    Tendsto
      (fun T : ℝ => ∫ t in Set.Icc (-T) T, φ t)
      atTop
      (𝓝 (∫ t : ℝ, φ t)) := by
  have hleft : Tendsto (fun T : ℝ => -T) atTop atBot :=
    tendsto_neg_atTop_atBot
  have hright : Tendsto (fun T : ℝ => T) atTop atTop :=
    tendsto_id
  have hcover :
      AECover (volume : Measure ℝ) atTop
        (fun T : ℝ => Set.Icc (-T) T) :=
    MeasureTheory.aecover_Icc hleft hright
  exact hcover.integral_tendsto_of_countably_generated hφ

/-- If an integrable kernel has a named whole-line value, its symmetric
truncations converge to that value. -/
theorem explicitFormulaSymmetricIntervalIntegral_tendsto_value
    (φ : ℝ → ℂ) (target : ℂ)
    (hφ : Integrable φ (volume : Measure ℝ))
    (hvalue : (∫ t : ℝ, φ t) = target) :
    Tendsto
      (fun T : ℝ => ∫ t in Set.Icc (-T) T, φ t)
      atTop
      (𝓝 target) := by
  exact Eq.subst
    (motive := fun z : ℂ =>
      Tendsto
        (fun T : ℝ => ∫ t in Set.Icc (-T) T, φ t)
        atTop
        (𝓝 z))
    hvalue
    (explicitFormulaSymmetricIntervalIntegral_tendsto_integral φ hφ)

/-- On a symmetric interval, the integral of a difference is the difference of
the integrals, assuming whole-line integrability of both kernels. -/
theorem explicitFormulaSymmetricIntervalIntegral_sub_eq_integral_sub
    (φ ψ : ℝ → ℂ)
    (hφ : Integrable φ (volume : Measure ℝ))
    (hψ : Integrable ψ (volume : Measure ℝ)) (T : ℝ) :
    (∫ t in Set.Icc (-T) T, φ t) -
        ∫ t in Set.Icc (-T) T, ψ t =
      ∫ t in Set.Icc (-T) T, φ t - ψ t := by
  have hφ_interval :
      Integrable φ
        ((volume : Measure ℝ).restrict (Set.Icc (-T) T)) :=
    (hφ.integrableOn).integrable
  have hψ_interval :
      Integrable ψ
        ((volume : Measure ℝ).restrict (Set.Icc (-T) T)) :=
    (hψ.integrableOn).integrable
  exact (integral_sub hφ_interval hψ_interval).symm

/-- Symmetric interval integrals of a difference of two integrable kernels
converge to the whole-line integral of their pointwise difference. -/
theorem zetaCompletedExplicitFormulaSymmetricIntegral_sub_tendsto_integral_sub
    (φ ψ : ℝ → ℂ)
    (hφ : Integrable φ (volume : Measure ℝ))
    (hψ : Integrable ψ (volume : Measure ℝ)) :
    Tendsto
      (fun T : ℝ =>
        (∫ t in Set.Icc (-T) T, φ t) -
          ∫ t in Set.Icc (-T) T, ψ t)
      atTop
      (𝓝 (∫ t : ℝ, φ t - ψ t)) := by
  let χ : ℝ → ℂ := fun t : ℝ => φ t - ψ t
  have hχ : Integrable χ (volume : Measure ℝ) :=
    hφ.sub hψ
  have hχ_tendsto :
      Tendsto
        (fun T : ℝ => ∫ t in Set.Icc (-T) T, χ t)
        atTop
        (𝓝 (∫ t : ℝ, χ t)) :=
    explicitFormulaSymmetricIntervalIntegral_tendsto_integral χ hχ
  have hpoint :
      (fun T : ℝ =>
        (∫ t in Set.Icc (-T) T, φ t) -
          ∫ t in Set.Icc (-T) T, ψ t) =
        (fun T : ℝ => ∫ t in Set.Icc (-T) T, χ t) := by
    exact funext
      (fun T : ℝ =>
        explicitFormulaSymmetricIntervalIntegral_sub_eq_integral_sub
          φ ψ hφ hψ T)
  exact
    Eq.subst
      (motive := fun g : ℝ → ℂ =>
        Tendsto g atTop (𝓝 (∫ t : ℝ, χ t)))
      hpoint.symm
      hχ_tendsto

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
