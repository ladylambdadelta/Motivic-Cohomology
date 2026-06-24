import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.AffineKernelIntegrability

/-!
# Integrable majorant packages for affine kernels

This file owns the measure-theoretic packaging shared by the affine vertical
kernel estimates.  Analytic files provide the actual pointwise majorants; this
file proves the reusable transport from those majorants to integrability and
under addition/subtraction of kernels.
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

/-- A complex kernel together with an integrable real-valued majorant. -/
structure ExplicitFormulaAffineKernelMajorantPackage (φ : ℝ → ℂ) where
  majorant : ℝ → ℝ
  integrable_majorant : Integrable majorant (volume : Measure ℝ)
  stronglyMeasurable_kernel : AEStronglyMeasurable φ (volume : Measure ℝ)
  norm_le_majorant :
    ∀ᵐ t ∂(volume : Measure ℝ), ‖φ t‖ ≤ majorant t

/-- The bundled majorant package implies kernel integrability. -/
theorem ExplicitFormulaAffineKernelMajorantPackage.integrable
    {φ : ℝ → ℂ} (P : ExplicitFormulaAffineKernelMajorantPackage φ) :
    Integrable φ (volume : Measure ℝ) :=
  explicitFormulaAffineKernel_integrable_of_integrable_majorant
    φ P.majorant P.integrable_majorant P.stronglyMeasurable_kernel
    P.norm_le_majorant

/-- The bundled majorant package exposes the old existential majorant shape. -/
theorem ExplicitFormulaAffineKernelMajorantPackage.exists_majorant
    {φ : ℝ → ℂ} (P : ExplicitFormulaAffineKernelMajorantPackage φ) :
    ∃ majorant : ℝ → ℝ,
      Integrable majorant (volume : Measure ℝ) ∧
        AEStronglyMeasurable φ (volume : Measure ℝ) ∧
        ∀ᵐ t ∂(volume : Measure ℝ), ‖φ t‖ ≤ majorant t :=
  ⟨P.majorant, P.integrable_majorant, P.stronglyMeasurable_kernel,
    P.norm_le_majorant⟩

/-- Build a majorant package from the old existential majorant shape. -/
def ExplicitFormulaAffineKernelMajorantPackage.of_exists
    {φ : ℝ → ℂ}
    (h :
      ∃ majorant : ℝ → ℝ,
        Integrable majorant (volume : Measure ℝ) ∧
          AEStronglyMeasurable φ (volume : Measure ℝ) ∧
          ∀ᵐ t ∂(volume : Measure ℝ), ‖φ t‖ ≤ majorant t) :
    ExplicitFormulaAffineKernelMajorantPackage φ :=
  match h with
  | ⟨majorant, hmajorant, hmeas, hbound⟩ =>
      { majorant := majorant
        integrable_majorant := hmajorant
        stronglyMeasurable_kernel := hmeas
        norm_le_majorant := hbound }

/-- The zero kernel has the zero integrable majorant. -/
def ExplicitFormulaAffineKernelMajorantPackage.zero :
    ExplicitFormulaAffineKernelMajorantPackage (fun _ : ℝ => (0 : ℂ)) :=
  { majorant := fun _ : ℝ => 0
    integrable_majorant := integrable_zero
    stronglyMeasurable_kernel :=
      aestronglyMeasurable_const
    norm_le_majorant :=
      Filter.Eventually.of_forall
        (fun _ : ℝ => le_of_eq (norm_zero : ‖(0 : ℂ)‖ = 0)) }

/-- Multiplication by a fixed complex scalar preserves integrable-majorant
packages. -/
def ExplicitFormulaAffineKernelMajorantPackage.const_mul
    {φ : ℝ → ℂ} (c : ℂ)
    (P : ExplicitFormulaAffineKernelMajorantPackage φ) :
    ExplicitFormulaAffineKernelMajorantPackage
      (fun t : ℝ => c * φ t) :=
  { majorant := fun t : ℝ => ‖c‖ * P.majorant t
    integrable_majorant := P.integrable_majorant.const_mul ‖c‖
    stronglyMeasurable_kernel :=
      P.stronglyMeasurable_kernel.const_mul c
    norm_le_majorant :=
      P.norm_le_majorant.mono
        (fun t ht =>
          calc
            ‖c * φ t‖ = ‖c‖ * ‖φ t‖ := norm_mul c (φ t)
            _ ≤ ‖c‖ * P.majorant t :=
                mul_le_mul_of_nonneg_left ht (norm_nonneg c)) }

/-- Right multiplication by a fixed complex scalar preserves
integrable-majorant packages. -/
def ExplicitFormulaAffineKernelMajorantPackage.mul_const
    {φ : ℝ → ℂ} (c : ℂ)
    (P : ExplicitFormulaAffineKernelMajorantPackage φ) :
    ExplicitFormulaAffineKernelMajorantPackage
      (fun t : ℝ => φ t * c) :=
  { majorant := fun t : ℝ => P.majorant t * ‖c‖
    integrable_majorant := P.integrable_majorant.mul_const ‖c‖
    stronglyMeasurable_kernel :=
      P.stronglyMeasurable_kernel.mul_const c
    norm_le_majorant :=
      P.norm_le_majorant.mono
        (fun t ht =>
          calc
            ‖φ t * c‖ = ‖φ t‖ * ‖c‖ := norm_mul (φ t) c
            _ ≤ P.majorant t * ‖c‖ :=
                mul_le_mul_of_nonneg_right ht (norm_nonneg c)) }

/-- Addition of two kernels preserves integrable-majorant packages. -/
def ExplicitFormulaAffineKernelMajorantPackage.add
    {φ ψ : ℝ → ℂ}
    (Pφ : ExplicitFormulaAffineKernelMajorantPackage φ)
    (Pψ : ExplicitFormulaAffineKernelMajorantPackage ψ) :
    ExplicitFormulaAffineKernelMajorantPackage
      (fun t : ℝ => φ t + ψ t) :=
  { majorant := fun t : ℝ => Pφ.majorant t + Pψ.majorant t
    integrable_majorant :=
      Pφ.integrable_majorant.add Pψ.integrable_majorant
    stronglyMeasurable_kernel :=
      Pφ.stronglyMeasurable_kernel.add Pψ.stronglyMeasurable_kernel
    norm_le_majorant :=
      (Pφ.norm_le_majorant.and Pψ.norm_le_majorant).mono
        (fun t ht =>
          calc
            ‖φ t + ψ t‖ ≤ ‖φ t‖ + ‖ψ t‖ := norm_add_le (φ t) (ψ t)
            _ ≤ Pφ.majorant t + Pψ.majorant t :=
                add_le_add ht.1 ht.2) }

/-- Negation preserves integrable-majorant packages. -/
def ExplicitFormulaAffineKernelMajorantPackage.neg
    {φ : ℝ → ℂ}
    (P : ExplicitFormulaAffineKernelMajorantPackage φ) :
    ExplicitFormulaAffineKernelMajorantPackage
      (fun t : ℝ => -φ t) :=
  { majorant := P.majorant
    integrable_majorant := P.integrable_majorant
    stronglyMeasurable_kernel := P.stronglyMeasurable_kernel.neg
    norm_le_majorant :=
      P.norm_le_majorant.mono
        (fun t ht =>
          Eq.subst
            (motive := fun x : ℝ => x ≤ P.majorant t)
            (norm_neg (φ t)).symm
            ht) }

/-- Subtraction of two kernels preserves integrable-majorant packages. -/
def ExplicitFormulaAffineKernelMajorantPackage.sub
    {φ ψ : ℝ → ℂ}
    (Pφ : ExplicitFormulaAffineKernelMajorantPackage φ)
    (Pψ : ExplicitFormulaAffineKernelMajorantPackage ψ) :
    ExplicitFormulaAffineKernelMajorantPackage
      (fun t : ℝ => φ t - ψ t) :=
  Pφ.add Pψ.neg

/-- A pointwise product majorant packages the product of two complex kernels.

The real majorant is supplied explicitly because analytic owner files choose the
decay exponent and prove its integrability. -/
def ExplicitFormulaAffineKernelMajorantPackage.of_mul_le
    {φ ψ : ℝ → ℂ} (majorant : ℝ → ℝ)
    (hintegrable : Integrable majorant (volume : Measure ℝ))
    (hφ : AEStronglyMeasurable φ (volume : Measure ℝ))
    (hψ : AEStronglyMeasurable ψ (volume : Measure ℝ))
    (hbound :
      ∀ᵐ t ∂(volume : Measure ℝ),
        ‖φ t‖ * ‖ψ t‖ ≤ majorant t) :
    ExplicitFormulaAffineKernelMajorantPackage
      (fun t : ℝ => φ t * ψ t) :=
  { majorant := majorant
    integrable_majorant := hintegrable
    stronglyMeasurable_kernel := hφ.mul hψ
    norm_le_majorant :=
      hbound.mono
        (fun t ht =>
          Eq.subst
            (motive := fun x : ℝ => x ≤ majorant t)
            (norm_mul (φ t) (ψ t)).symm
            ht) }

/-- A pointwise product majorant packages the product in the opposite order. -/
def ExplicitFormulaAffineKernelMajorantPackage.of_le_mul
    {φ ψ : ℝ → ℂ} (majorant : ℝ → ℝ)
    (hintegrable : Integrable majorant (volume : Measure ℝ))
    (hφ : AEStronglyMeasurable φ (volume : Measure ℝ))
    (hψ : AEStronglyMeasurable ψ (volume : Measure ℝ))
    (hbound :
      ∀ᵐ t ∂(volume : Measure ℝ),
        ‖φ t‖ * ‖ψ t‖ ≤ majorant t) :
    ExplicitFormulaAffineKernelMajorantPackage
      (fun t : ℝ => ψ t * φ t) :=
  { majorant := majorant
    integrable_majorant := hintegrable
    stronglyMeasurable_kernel := hψ.mul hφ
    norm_le_majorant :=
      hbound.mono
        (fun t ht =>
          Eq.subst
            (motive := fun x : ℝ => x ≤ majorant t)
            (Eq.trans
              (norm_mul (ψ t) (φ t))
              (mul_comm ‖ψ t‖ ‖φ t‖)).symm
            ht) }

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
