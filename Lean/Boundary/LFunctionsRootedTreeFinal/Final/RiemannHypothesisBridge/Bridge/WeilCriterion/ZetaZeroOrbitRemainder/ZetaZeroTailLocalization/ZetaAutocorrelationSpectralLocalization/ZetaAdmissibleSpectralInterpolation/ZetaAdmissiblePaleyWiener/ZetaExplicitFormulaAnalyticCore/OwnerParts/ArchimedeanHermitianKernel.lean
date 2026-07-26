import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaAdmissibleSpectralInterpolation.ZetaAdmissiblePaleyWiener.ZetaExplicitFormulaAnalyticCore.OwnerParts.ArchimedeanCenteredKernel

/-!
# Hermitian critical-line archimedean kernel

The completed two-face contour contributes the pair of critical-line Gamma
channels.  This file owns that pair before it is converted to a real signed
weight.  The older centered integrand remains the individual positive-height
channel and is not used as a replacement for the pair.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open Complex
open MeasureTheory

namespace ZetaAdmissibleFunction

/-- The Hermitian pair of the completed archimedean logarithmic derivative on
the critical line. -/
noncomputable def zetaCompletedArchimedeanHermitianKernel
    (t : ℝ) : ℂ :=
  zetaCompletedArchimedeanLogDerivativeKernel
      (zetaCompletedCenteredSpectralLine t) +
    star
      (zetaCompletedArchimedeanLogDerivativeKernel
        (zetaCompletedCenteredSpectralLine t))

/-- The Hermitian critical-line archimedean integrand. -/
noncomputable def zetaCompletedArchimedeanHermitianIntegrand
    (f : ZetaAdmissibleFunction)
    (t : ℝ) : ℂ :=
  zetaCompletedArchimedeanHermitianKernel t *
    zetaCompletedExplicitFormulaPhi f (t * Complex.I)

/-- The completed two-face archimedean distribution. -/
noncomputable def zetaCompletedExplicitFormulaHermitianArchimedeanContribution
    (f : ZetaAdmissibleFunction) : ℂ :=
  ∫ t : ℝ, zetaCompletedArchimedeanHermitianIntegrand f t

/-- The Hermitian integrand unfolds to the sum of the critical-line channel
and its conjugate channel. -/
theorem zetaCompletedArchimedeanHermitianIntegrand_eq
    (f : ZetaAdmissibleFunction)
    (t : ℝ) :
    zetaCompletedArchimedeanHermitianIntegrand f t =
      (zetaCompletedArchimedeanLogDerivativeKernel
          (zetaCompletedCenteredSpectralLine t) +
        star
          (zetaCompletedArchimedeanLogDerivativeKernel
            (zetaCompletedCenteredSpectralLine t))) *
        zetaCompletedExplicitFormulaPhi f (t * Complex.I) := by
  exact Eq.refl _

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
