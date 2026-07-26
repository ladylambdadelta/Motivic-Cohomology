import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaZeroKreinGram.WeilCriterion.OwnerParts.CompletedHermitianInverseGamma
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaZeroKreinGram.WeilCriterion.OwnerParts.CompletedAffineArchimedeanValue
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaZeroKreinGram.WeilCriterion.OwnerParts.CompletedAffineRegularContourTransport

/-!
# Regular affine inverse-Gamma transport

The coupled inverse-Gamma logarithmic derivative is shifted before its
meromorphic archimedean and rational correction subchannels are separated.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open MeasureTheory

namespace ZetaAdmissibleFunction

/-- The coupled regular inverse-Gamma packet transports to the Hermitian
critical-line inverse-Gamma packet; the archimedean residue and elementary
correction cancel before transport. -/
theorem zetaCompletedAffineInverseGamma_integral_eq_hermitianInverseGamma_owner
    (f : ZetaAdmissibleFunction)
    (hPhi : ZetaPhiAnalyticControl (convolutionAutocorrelation f))
    (hLog : CompletedZetaNegLogDerivControl (convolutionAutocorrelation f)) :
    let probe : ZetaAdmissibleFunction := convolutionAutocorrelation f
    let family : ExplicitFormulaContourFamily :=
      zetaCompletedExplicitFormula_autocorrelation_contourFamily f
    (∫ t : ℝ,
      zetaCompletedAffineInverseGammaRightReflectedDifferenceKernel
        probe family t) =
      ∫ t : ℝ,
        zetaCompletedHermitianInverseGammaIntegrand probe t :=
  zetaCompletedAffineRegularInverseGamma_integral_eq_critical_owner f hPhi hLog

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
