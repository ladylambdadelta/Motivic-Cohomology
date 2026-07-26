import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaZeroTail.WeightedTail.Annihilator.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaZeroTail.ZetaPrimeRapidPower.ZetaPrimeTwoFaceCoordinates.ZetaPrimeContourTomography.TomographyRoot.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaCompletedLogDerivativeControl.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaAdmissibleSpectralInterpolation.ZetaAdmissiblePaleyWiener.ZetaExplicitFormulaAnalyticCore.OwnerParts.BoundaryChannels
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaAdmissibleSpectralInterpolation.ZetaAdmissiblePaleyWiener.ZetaExplicitFormulaAnalyticCore.OwnerParts.PrimePowerCoordinates

namespace Boundary
namespace LFunctions
noncomputable section
namespace ZetaAdmissibleFunction

abbrev ZetaCompletedZeroCoordinateLInfinity :=
  lp (fun rhoCoordinate : ZetaCompletedZeroCoordinate => ℂ) (⊤ : ENNReal)

noncomputable def completedPrimeTraceTimeScalar (f : ZetaAdmissibleFunction) : ℝ :=
  Complex.re (zetaCompletedExplicitFormulaPrimePowerContribution (convolutionAutocorrelation f))

noncomputable def completedPrimeTraceSpectralScalar (f : ZetaAdmissibleFunction) : ℝ :=
  Complex.re (zetaCompletedExplicitFormulaPrimePowerSpectralSampleContribution (convolutionAutocorrelation f))

theorem completedPrimeTraceTimeScalar_eq (f : ZetaAdmissibleFunction) :
    completedPrimeTraceTimeScalar f =
      Complex.re (zetaCompletedExplicitFormulaPrimePowerContribution (convolutionAutocorrelation f)) :=
  Eq.refl (completedPrimeTraceTimeScalar f)

theorem completedPrimeTraceSpectralScalar_eq (f : ZetaAdmissibleFunction) :
    completedPrimeTraceSpectralScalar f =
      Complex.re (zetaCompletedExplicitFormulaPrimePowerSpectralSampleContribution (convolutionAutocorrelation f)) :=
  Eq.refl (completedPrimeTraceSpectralScalar f)

noncomputable def completedPrimeTraceFunctionalGap (f : ZetaAdmissibleFunction) : ℝ :=
  Complex.re (zetaCompletedExplicitFormulaPrimePowerContribution (convolutionAutocorrelation f)) -
    Complex.re (zetaCompletedExplicitFormulaPrimePowerSpectralSampleContribution (convolutionAutocorrelation f))

theorem completedPrimeTraceFunctionalGap_eq (f : ZetaAdmissibleFunction) :
    completedPrimeTraceFunctionalGap f =
      Complex.re (zetaCompletedExplicitFormulaPrimePowerContribution (convolutionAutocorrelation f)) -
        Complex.re (zetaCompletedExplicitFormulaPrimePowerSpectralSampleContribution (convolutionAutocorrelation f)) :=
  Eq.refl (completedPrimeTraceFunctionalGap f)

end ZetaAdmissibleFunction
end
end LFunctions
end Boundary
