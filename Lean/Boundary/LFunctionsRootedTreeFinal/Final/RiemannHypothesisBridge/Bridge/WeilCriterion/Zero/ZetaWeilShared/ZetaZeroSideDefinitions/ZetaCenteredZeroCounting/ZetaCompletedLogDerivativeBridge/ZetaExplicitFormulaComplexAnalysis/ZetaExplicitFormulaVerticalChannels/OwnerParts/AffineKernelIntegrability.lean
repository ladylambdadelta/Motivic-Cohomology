import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.AffineVerticalKernels

/-!
# Affine kernel integrability helpers

This file owns the measure-theoretic step from a concrete integrable majorant
to integrability of an affine vertical kernel.  Channel files own the analytic
construction of the majorants for their specific kernels.
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

/-- An affine kernel is integrable once it is a.e. strongly measurable and
bounded by an integrable real majorant. -/
theorem explicitFormulaAffineKernel_integrable_of_integrable_majorant
    (φ : ℝ → ℂ) (majorant : ℝ → ℝ)
    (hmajorant : Integrable majorant (volume : Measure ℝ))
    (hφ_meas : AEStronglyMeasurable φ (volume : Measure ℝ))
    (hbound : ∀ᵐ t ∂(volume : Measure ℝ), ‖φ t‖ ≤ majorant t) :
    Integrable φ (volume : Measure ℝ) :=
  hmajorant.mono' hφ_meas hbound

/-- Pointwise bounds are a convenient special case of the a.e. majorant
criterion. -/
theorem explicitFormulaAffineKernel_integrable_of_pointwise_integrable_majorant
    (φ : ℝ → ℂ) (majorant : ℝ → ℝ)
    (hmajorant : Integrable majorant (volume : Measure ℝ))
    (hφ_meas : AEStronglyMeasurable φ (volume : Measure ℝ))
    (hbound : ∀ t : ℝ, ‖φ t‖ ≤ majorant t) :
    Integrable φ (volume : Measure ℝ) :=
  explicitFormulaAffineKernel_integrable_of_integrable_majorant
    φ majorant hmajorant hφ_meas (Filter.Eventually.of_forall hbound)

/-- Integrability is unchanged by replacing an affine kernel with an a.e.-equal
kernel.  This small wrapper keeps downstream finite-exception arguments from
depending directly on the global name of mathlib's congruence theorem. -/
theorem explicitFormulaAffineKernel_integrable_congr_ae
    (φ ψ : ℝ → ℂ)
    (hφ : Integrable φ (volume : Measure ℝ))
    (hφψ : φ =ᵐ[(volume : Measure ℝ)] ψ) :
    Integrable ψ (volume : Measure ℝ) :=
  hφ.congr hφψ

/-- Two affine kernels that agree away from one real parameter are a.e.-equal
for Lebesgue measure.  This is the basic finite-exception transport needed for
vertical lines that may pass through an isolated Gamma pole at central height. -/
theorem explicitFormulaAffineKernel_ae_eq_of_eq_off_singleton
    (a : ℝ) (φ ψ : ℝ → ℂ)
    (hφψ : ∀ t : ℝ, t ≠ a → φ t = ψ t) :
    φ =ᵐ[(volume : Measure ℝ)] ψ := by
  have hnull : (volume : Measure ℝ) ({a} : Set ℝ) = 0 :=
    measure_singleton a
  have hcompl : {a}ᶜ ∈ ae (volume : Measure ℝ) :=
    compl_mem_ae_iff.mpr hnull
  exact Filter.mem_of_superset hcompl
    (fun t ht =>
      hφψ t
        (fun hta : t = a =>
          ht (Set.mem_singleton_iff.mpr hta)))

/-- Integrability is unchanged by replacing an affine kernel away from one real
parameter. -/
theorem explicitFormulaAffineKernel_integrable_congr_off_singleton
    (a : ℝ) (φ ψ : ℝ → ℂ)
    (hφ : Integrable φ (volume : Measure ℝ))
    (hφψ : ∀ t : ℝ, t ≠ a → φ t = ψ t) :
    Integrable ψ (volume : Measure ℝ) :=
  explicitFormulaAffineKernel_integrable_congr_ae
    φ ψ hφ
    (explicitFormulaAffineKernel_ae_eq_of_eq_off_singleton a φ ψ hφψ)

/-- A pointwise majorant outside one real parameter is enough for affine-kernel
integrability, since that exceptional singleton has Lebesgue measure zero. -/
theorem explicitFormulaAffineKernel_integrable_of_pointwise_majorant_off_singleton
    (a : ℝ) (φ : ℝ → ℂ) (majorant : ℝ → ℝ)
    (hmajorant : Integrable majorant (volume : Measure ℝ))
    (hφ_meas : AEStronglyMeasurable φ (volume : Measure ℝ))
    (hbound : ∀ t : ℝ, t ≠ a → ‖φ t‖ ≤ majorant t) :
    Integrable φ (volume : Measure ℝ) := by
  have hnull : (volume : Measure ℝ) ({a} : Set ℝ) = 0 :=
    measure_singleton a
  have hcompl : {a}ᶜ ∈ ae (volume : Measure ℝ) :=
    compl_mem_ae_iff.mpr hnull
  have hae_bound :
      ∀ᵐ t ∂(volume : Measure ℝ), ‖φ t‖ ≤ majorant t :=
    Filter.mem_of_superset hcompl
      (fun t ht =>
        hbound t
          (fun hta : t = a =>
            ht (Set.mem_singleton_iff.mpr hta)))
  exact
    explicitFormulaAffineKernel_integrable_of_integrable_majorant
      φ majorant hmajorant hφ_meas hae_bound

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
