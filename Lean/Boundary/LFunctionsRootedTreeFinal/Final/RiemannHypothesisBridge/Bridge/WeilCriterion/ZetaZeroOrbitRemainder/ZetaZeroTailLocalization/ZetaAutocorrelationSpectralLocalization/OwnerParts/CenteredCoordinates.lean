import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.Core

namespace Boundary
namespace LFunctions
noncomputable section
namespace ZetaAdmissibleFunction

/-- A finite spectral sample set translated into coordinates centered at `c`. -/
def translatedSpectralSampleFinset
    (P : Finset ℂ) (c : ℝ) : Finset ℂ :=
  P.image (fun z : ℂ => z - (c : ℂ))

/-- The RH localization contribution in centered spectral coordinates. -/
def zetaCenteredZeroSideContribution
    (rho : ℂ) (phi : ZetaAdmissibleFunction) : ℂ :=
  - (zetaZeroMultiplicity rho : ℂ) *
    zetaSpectralEval phi (zetaCenteredZero rho)

/-- The RH localization tail indexed by completed zeros in centered coordinates. -/
def zetaCenteredZeroTail
    (S : Finset ℂ) (phi : ZetaAdmissibleFunction) : ℂ :=
  tsum (fun eta : {eta : ℂ // ZetaCompletedZero eta ∧ eta ∉ S} =>
    zetaCenteredZeroSideContribution (eta : ℂ) phi)

end ZetaAdmissibleFunction
end
end LFunctions
end Boundary
