import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaCompletedLogDerivativeControl.FactorBoundData

namespace Boundary
namespace LFunctions
namespace ZetaAdmissibleFunction

noncomputable section

def CompletedZetaNegLogDerivZetaSideControl.ofFactorBoundData_owner
    (data :
      ∀ (a b : ℝ) (E : CompletedZetaZeroExcisedStrip a b),
        CompletedZetaZeroExcisedStrip.FactorBoundData E) :
    CompletedZetaNegLogDerivZetaSideControl :=
  CompletedZetaNegLogDerivZetaSideControl.ofBoundData_owner
    (fun a b E => (data a b E).zetaSide)

def CompletedZetaNegLogDerivInverseGammaControl.ofFactorBoundData_owner
    (data :
      ∀ (a b : ℝ) (E : CompletedZetaZeroExcisedStrip a b),
        CompletedZetaZeroExcisedStrip.FactorBoundData E) :
    CompletedZetaNegLogDerivInverseGammaControl :=
  CompletedZetaNegLogDerivInverseGammaControl.ofBoundData_owner
    (fun a b E => (data a b E).inverseGamma)

def completedZetaNegLogDerivAutocorrelationConcreteControl_of_factorBoundData_owner
    (data :
      ∀ (a b : ℝ) (E : CompletedZetaZeroExcisedStrip a b),
        CompletedZetaZeroExcisedStrip.FactorBoundData E) :
    CompletedZetaNegLogDerivAutocorrelationConcreteControl :=
  completedZetaNegLogDerivAutocorrelationConcreteControl_of_globalFactorControls
    (CompletedZetaNegLogDerivZetaSideControl.ofFactorBoundData_owner data)
    (CompletedZetaNegLogDerivInverseGammaControl.ofFactorBoundData_owner data)

end

end ZetaAdmissibleFunction
end LFunctions
end Boundary
