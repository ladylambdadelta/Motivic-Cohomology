import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.BasicChannels
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaAdmissibleSpectralInterpolation.ZetaAdmissiblePaleyWiener.VerticalIntegrationByParts.Owner

/-!
# Phi vertical-line kernel transport

This file owns the local transport from the explicit-formula notation `Φ_f`
to the Paley-Wiener vertical-line kernel integral.  The theorem is a
normalization helper for the zero-pole inversion channel: it records only what
already follows from the Laplace-transform definition of `Φ_f` and the
Paley-Wiener vertical decomposition.
-/

namespace Boundary
namespace LFunctions

noncomputable section

namespace ZetaAdmissibleFunction

/-- The explicit-formula spectral transform is the vertical-line kernel
integral attached to its real and imaginary coordinates. -/
theorem zetaCompletedExplicitFormulaPhi_eq_verticalLineKernelIntegral
    (f : ZetaAdmissibleFunction) (z : ℂ) :
    zetaCompletedExplicitFormulaPhi f z =
      ∫ t : ℝ, zetaPaleyWienerVerticalLineKernel f z.re z.im t := by
  have hphi :
      zetaCompletedExplicitFormulaPhi f z =
        Boundary.zetaLaplaceTransform f.toZetaTestFunction' z := by
    exact congrFun (zetaCompletedExplicitFormulaPhi_eq_laplace f) z
  have hlaplace :
      Boundary.zetaLaplaceTransform f.toZetaTestFunction' z =
        ∫ t : ℝ, zetaPaleyWienerVerticalLineKernel f z.re z.im t :=
    zetaLaplaceTransform_eq_verticalLineKernelIntegral f z
  exact hphi.trans hlaplace

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
