import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.InverseGammaBranchFactorBounds
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.InverseGammaAffineKernelEstimate

/-!
# Branch inverse-Gamma affine-kernel estimates

This file owns branch-coherence majorant packages for the inverse-Gamma affine
kernels, assembled from the branch fixed-line factor bounds.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open Complex
open LSeries ArithmeticFunction
open MeasureTheory
open scoped ArithmeticFunction

namespace ZetaAdmissibleFunction

/-- Branch-coherence majorant package for the right inverse-Gamma affine
kernel. -/
def zetaCompletedExplicitFormulaInverseGammaRightAffineKernel_majorantPackage_of_branchBinet
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (hbranch : Complex.binetBranchLogGammaCoherence) :
    ExplicitFormulaAffineKernelMajorantPackage
      (zetaCompletedExplicitFormulaInverseGammaRightAffineKernel f F) :=
  Eq.ndrec
    (motive := fun branchData : Complex.binetBranchLogGammaCoherence =>
      ExplicitFormulaAffineKernelMajorantPackage
        (zetaCompletedExplicitFormulaInverseGammaRightAffineKernel f F))
    (zetaCompletedExplicitFormulaInverseGammaRightAffineKernel_majorantPackage_of_gammaBinet
      f F h)
    (Eq.refl hbranch)

/-- Branch-coherence majorant package for the left inverse-Gamma affine
kernel. -/
def zetaCompletedExplicitFormulaInverseGammaLeftAffineKernel_majorantPackage_of_branchBinet
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (hregular : zetaCompletedExplicitFormulaLeftAffineLineGammaRegular F)
    (hbranch : Complex.binetBranchLogGammaCoherence) :
    ExplicitFormulaAffineKernelMajorantPackage
      (zetaCompletedExplicitFormulaInverseGammaLeftAffineKernel f F) :=
  Eq.ndrec
    (motive := fun branchData : Complex.binetBranchLogGammaCoherence =>
      ExplicitFormulaAffineKernelMajorantPackage
        (zetaCompletedExplicitFormulaInverseGammaLeftAffineKernel f F))
    (zetaCompletedExplicitFormulaInverseGammaLeftAffineKernel_majorantPackage_of_gammaBinet
      f F h hregular)
    (Eq.refl hbranch)

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
