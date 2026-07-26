import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.InverseGammaAffineKernelEstimateGammaBinet
/-!
# Inverse-Gamma affine-kernel estimate split part

This file is a mechanical owner split of the inverse-Gamma affine-kernel estimate.
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

/-- Bundled majorant package for the right inverse-Gamma affine kernel. -/
def zetaCompletedExplicitFormulaInverseGammaRightAffineKernel_majorantPackage
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) :
    ExplicitFormulaAffineKernelMajorantPackage
      (zetaCompletedExplicitFormulaInverseGammaRightAffineKernel f F) :=
  zetaCompletedExplicitFormulaInverseGammaRightAffineKernel_majorantPackage_of_gammaBinet
    f F h

/-- Gamma/Binet-coherence-qualified existential majorant package for the right
inverse-Gamma affine kernel. -/
theorem zetaCompletedExplicitFormulaInverseGammaRightAffineKernel_integrableMajorant_of_gammaBinet
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) :
    ∃ majorant : ℝ → ℝ,
      Integrable majorant (volume : Measure ℝ) ∧
        AEStronglyMeasurable
          (zetaCompletedExplicitFormulaInverseGammaRightAffineKernel f F)
          (volume : Measure ℝ) ∧
        ∀ᵐ t ∂(volume : Measure ℝ),
          ‖zetaCompletedExplicitFormulaInverseGammaRightAffineKernel f F t‖
            ≤ majorant t :=
  (zetaCompletedExplicitFormulaInverseGammaRightAffineKernel_majorantPackage_of_gammaBinet
    f F h).exists_majorant

/-- Gamma/Binet-coherence-qualified integrability of the right inverse-Gamma
affine kernel. -/
theorem zetaCompletedExplicitFormulaInverseGammaRightAffineKernel_integrable_of_gammaBinet
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) :
    Integrable
      (zetaCompletedExplicitFormulaInverseGammaRightAffineKernel f F)
      (volume : Measure ℝ) :=
  (zetaCompletedExplicitFormulaInverseGammaRightAffineKernel_majorantPackage_of_gammaBinet
    f F h).integrable

/-- Gamma/Binet owner-level integrability of the right inverse-Gamma affine
kernel from direct transform control. -/
theorem zetaCompletedExplicitFormulaInverseGammaRightAffineKernel_integrable_of_phiControl_gammaBinet
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (hPhi : ZetaPhiAnalyticControl f) :
    Integrable
      (zetaCompletedExplicitFormulaInverseGammaRightAffineKernel f F)
      (volume : Measure ℝ) :=
  Exists.elim
    (zetaCompletedExplicitFormulaInverseGammaCompletionLogDeriv_rightAffineLine_bound_of_gammaBinet_owner
      F)
    (fun B hB_data =>
      (zetaCompletedExplicitFormulaInverseGammaRightAffineKernel_majorantPackage_of_phiControl_factor_bound
        f F hPhi B hB_data.left hB_data.right).integrable)

/-- Existential majorant package for the right inverse-Gamma affine kernel. -/
theorem zetaCompletedExplicitFormulaInverseGammaRightAffineKernel_integrableMajorant
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) :
    ∃ majorant : ℝ → ℝ,
      Integrable majorant (volume : Measure ℝ) ∧
        AEStronglyMeasurable
          (zetaCompletedExplicitFormulaInverseGammaRightAffineKernel f F)
          (volume : Measure ℝ) ∧
        ∀ᵐ t ∂(volume : Measure ℝ),
          ‖zetaCompletedExplicitFormulaInverseGammaRightAffineKernel f F t‖
            ≤ majorant t :=
  (zetaCompletedExplicitFormulaInverseGammaRightAffineKernel_majorantPackage
    f F h).exists_majorant

/-- Integrability of the right inverse-Gamma affine kernel. -/
theorem zetaCompletedExplicitFormulaInverseGammaRightAffineKernel_integrable
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) :
    Integrable
      (zetaCompletedExplicitFormulaInverseGammaRightAffineKernel f F)
      (volume : Measure ℝ) :=
  (zetaCompletedExplicitFormulaInverseGammaRightAffineKernel_majorantPackage
    f F h).integrable

/-- Bundled majorant package for the left inverse-Gamma affine kernel. -/
def zetaCompletedExplicitFormulaInverseGammaLeftAffineKernel_majorantPackage
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (hregular : zetaCompletedExplicitFormulaLeftAffineLineGammaRegular F) :
    ExplicitFormulaAffineKernelMajorantPackage
      (zetaCompletedExplicitFormulaInverseGammaLeftAffineKernel f F) :=
  zetaCompletedExplicitFormulaInverseGammaLeftAffineKernel_majorantPackage_of_gammaBinet
    f F h hregular

/-- Regular Gamma/Binet-coherence-qualified existential majorant package for
the left inverse-Gamma affine kernel. -/
theorem zetaCompletedExplicitFormulaInverseGammaLeftAffineKernel_integrableMajorant_of_gammaBinet_regular
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (hregular : zetaCompletedExplicitFormulaLeftAffineLineGammaRegular F) :
    ∃ majorant : ℝ → ℝ,
      Integrable majorant (volume : Measure ℝ) ∧
        AEStronglyMeasurable
          (zetaCompletedExplicitFormulaInverseGammaLeftAffineKernel f F)
          (volume : Measure ℝ) ∧
        ∀ᵐ t ∂(volume : Measure ℝ),
          ‖zetaCompletedExplicitFormulaInverseGammaLeftAffineKernel f F t‖
            ≤ majorant t :=
  (zetaCompletedExplicitFormulaInverseGammaLeftAffineKernel_majorantPackage_of_gammaBinet
    f F h hregular).exists_majorant

/-- Regular Gamma/Binet-coherence-qualified integrability of the left
inverse-Gamma affine kernel. -/
theorem zetaCompletedExplicitFormulaInverseGammaLeftAffineKernel_integrable_of_gammaBinet_regular
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (hregular : zetaCompletedExplicitFormulaLeftAffineLineGammaRegular F) :
    Integrable
      (zetaCompletedExplicitFormulaInverseGammaLeftAffineKernel f F)
      (volume : Measure ℝ) :=
  (zetaCompletedExplicitFormulaInverseGammaLeftAffineKernel_majorantPackage_of_gammaBinet
    f F h hregular).integrable

/-- Existential majorant package for the left inverse-Gamma affine kernel. -/
theorem zetaCompletedExplicitFormulaInverseGammaLeftAffineKernel_integrableMajorant
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (hregular : zetaCompletedExplicitFormulaLeftAffineLineGammaRegular F) :
    ∃ majorant : ℝ → ℝ,
      Integrable majorant (volume : Measure ℝ) ∧
        AEStronglyMeasurable
          (zetaCompletedExplicitFormulaInverseGammaLeftAffineKernel f F)
          (volume : Measure ℝ) ∧
        ∀ᵐ t ∂(volume : Measure ℝ),
          ‖zetaCompletedExplicitFormulaInverseGammaLeftAffineKernel f F t‖
            ≤ majorant t :=
  (zetaCompletedExplicitFormulaInverseGammaLeftAffineKernel_majorantPackage
    f F h hregular).exists_majorant

/-- Integrability of the left inverse-Gamma affine kernel. -/
theorem zetaCompletedExplicitFormulaInverseGammaLeftAffineKernel_integrable
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (hregular : zetaCompletedExplicitFormulaLeftAffineLineGammaRegular F) :
    Integrable
      (zetaCompletedExplicitFormulaInverseGammaLeftAffineKernel f F)
      (volume : Measure ℝ) :=
  (zetaCompletedExplicitFormulaInverseGammaLeftAffineKernel_majorantPackage
    f F h hregular).integrable

/-- Bundled majorant package for the right-minus-left inverse-Gamma affine
kernel. -/
def zetaCompletedExplicitFormulaInverseGammaDifferenceAffineKernel_majorantPackage
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (hregular : zetaCompletedExplicitFormulaLeftAffineLineGammaRegular F) :
    ExplicitFormulaAffineKernelMajorantPackage
      (zetaCompletedExplicitFormulaInverseGammaDifferenceAffineKernel f F) :=
  (zetaCompletedExplicitFormulaInverseGammaRightAffineKernel_majorantPackage
    f F h).sub
    (zetaCompletedExplicitFormulaInverseGammaLeftAffineKernel_majorantPackage
      f F h hregular)

/-- Regular, Gamma-coherence-qualified bundled majorant package for the
right-minus-left inverse-Gamma affine kernel.  This is the honest analytic path:
the right side uses the positive half-plane Binet estimate, while the left side
uses finite recurrence shift and requires the left half-line to avoid Gamma
poles. -/
def zetaCompletedExplicitFormulaInverseGammaDifferenceAffineKernel_majorantPackage_of_gammaBinet_regular
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (hregular : zetaCompletedExplicitFormulaLeftAffineLineGammaRegular F) :
    ExplicitFormulaAffineKernelMajorantPackage
      (zetaCompletedExplicitFormulaInverseGammaDifferenceAffineKernel f F) :=
  (zetaCompletedExplicitFormulaInverseGammaRightAffineKernel_majorantPackage_of_gammaBinet
    f F h).sub
    (zetaCompletedExplicitFormulaInverseGammaLeftAffineKernel_majorantPackage_of_gammaBinet
      f F h hregular)

/-- Integrability of the right-minus-left inverse-Gamma affine kernel. -/
theorem zetaCompletedExplicitFormulaInverseGammaDifferenceAffineKernel_integrable
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (hregular : zetaCompletedExplicitFormulaLeftAffineLineGammaRegular F) :
    Integrable
      (zetaCompletedExplicitFormulaInverseGammaDifferenceAffineKernel f F)
      (volume : Measure ℝ) :=
  (zetaCompletedExplicitFormulaInverseGammaDifferenceAffineKernel_majorantPackage
    f F h hregular).integrable

/-- Regular, Gamma-coherence-qualified integrability of the right-minus-left
inverse-Gamma affine kernel. -/
theorem zetaCompletedExplicitFormulaInverseGammaDifferenceAffineKernel_integrable_of_gammaBinet_regular
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (hregular : zetaCompletedExplicitFormulaLeftAffineLineGammaRegular F) :
    Integrable
      (zetaCompletedExplicitFormulaInverseGammaDifferenceAffineKernel f F)
      (volume : Measure ℝ) :=
  (zetaCompletedExplicitFormulaInverseGammaDifferenceAffineKernel_majorantPackage_of_gammaBinet_regular
    f F h hregular).integrable

/-- Vertically regular, Gamma-coherence-qualified integrability of the
right-minus-left inverse-Gamma affine kernel. -/
theorem zetaCompletedExplicitFormulaInverseGammaDifferenceAffineKernel_integrable_of_verticallyRegular_gammaBinet
    (f : ZetaAdmissibleFunction)
    (F : ExplicitFormulaVerticallyRegularContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F.toContourFamily) :
    Integrable
      (zetaCompletedExplicitFormulaInverseGammaDifferenceAffineKernel
        f F.toContourFamily)
      (volume : Measure ℝ) :=
  zetaCompletedExplicitFormulaInverseGammaDifferenceAffineKernel_integrable_of_gammaBinet_regular
    f F.toContourFamily h
    (zetaCompletedExplicitFormulaLeftAffineLineGammaRegular_of_verticallyRegular
      F)

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
