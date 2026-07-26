import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.OwnerParts.PresentationParts.Part01_ValueDefinitions
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.OwnerParts.CenteredZeroTail

namespace Boundary
namespace LFunctions
noncomputable section
namespace ZetaAdmissibleFunction

def autocorrelationCenteredZeroTailRealAbs
    (S : Finset ℂ) (f : ZetaAdmissibleFunction) : ℝ :=
  |Complex.re (zetaCenteredZeroTail S (convolutionAutocorrelation f))|

theorem autocorrelationCenteredZeroTailRealAbs_eq
    (S : Finset ℂ) (f : ZetaAdmissibleFunction) :
    autocorrelationCenteredZeroTailRealAbs S f =
      |Complex.re (zetaCenteredZeroTail S (convolutionAutocorrelation f))| :=
  Eq.refl (autocorrelationCenteredZeroTailRealAbs S f)

theorem autocorrelationCenteredZeroTailRealAbs_le_centeredTailNorm
    (S : Finset ℂ) (f : ZetaAdmissibleFunction) :
    autocorrelationCenteredZeroTailRealAbs S f ≤
      ‖zetaCenteredZeroTail S (convolutionAutocorrelation f)‖ :=
  RCLike.abs_re_le_norm
    (zetaCenteredZeroTail S (convolutionAutocorrelation f))

theorem autocorrelationCenteredZeroTailRealAbs_lt_of_centeredTailNorm_lt
    (S : Finset ℂ)
    (f : ZetaAdmissibleFunction)
    (ε : ℝ)
    (htail :
      ‖zetaCenteredZeroTail S (convolutionAutocorrelation f)‖ < ε) :
    autocorrelationCenteredZeroTailRealAbs S f < ε :=
  lt_of_le_of_lt
    (autocorrelationCenteredZeroTailRealAbs_le_centeredTailNorm S f)
    htail

end ZetaAdmissibleFunction
end
end LFunctions
end Boundary
