import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaZeroTail.ZetaPrimeRapidPower.ZetaPrimeTwoFaceCoordinates.ZetaPrimeContourTomography.CoordinateLedger.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaZeroTail.ZetaPrimeRapidPower.ZetaPrimeTwoFaceCoordinates.ZetaPrimeContourTomography.CoordinateLedger.HeightSchedule

/-!
# Concrete completed prime residue shadow

This owner part contains only the concrete specialization of the
schedule-parametric horizontal residue shadow to the completed-prime height
schedule.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open Filter
open scoped Topology

namespace ZetaAdmissibleFunction

/-- The concrete finite prime horizontal residue shadow is the scheduled
horizontal residue shadow at the completed-prime owner height schedule. -/
noncomputable def finitePrimeHorizontalResidueShadow
    (N : ℕ) (f : ZetaAdmissibleFunction) : ℝ :=
  finitePrimeHorizontalResidueShadowAt
    completedPrimeContourTransportHeightSchedule_owner N f

/-- The concrete finite prime horizontal residue shadow unfolds to the
canonical scheduled horizontal residue shadow. -/
theorem finitePrimeHorizontalResidueShadow_eq_shadowAt_ownerSchedule
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    finitePrimeHorizontalResidueShadow N f =
      finitePrimeHorizontalResidueShadowAt
        completedPrimeContourTransportHeightSchedule_owner N f :=
  Eq.refl (finitePrimeHorizontalResidueShadow N f)

/-- The concrete finite prime horizontal residue shadow is the real part of
the completed-prime scheduled horizontal residue-window error. -/
theorem finitePrimeHorizontalResidueShadow_eq_horizontalResidueWindowError_re
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    finitePrimeHorizontalResidueShadow N f =
      Complex.re
        (explicitFormulaFamilyHorizontalResidueWindowError
          (convolutionAutocorrelation f)
          completedPrimeContourTransportFamily
          (completedPrimeContourTransportHeightSchedule_owner.height (N : ℝ))) :=
  let hshadowAt :
      finitePrimeHorizontalResidueShadow N f =
        finitePrimeHorizontalResidueShadowAt
          completedPrimeContourTransportHeightSchedule_owner N f :=
    finitePrimeHorizontalResidueShadow_eq_shadowAt_ownerSchedule N f
  let hunfold :
      finitePrimeHorizontalResidueShadowAt
          completedPrimeContourTransportHeightSchedule_owner N f =
        Complex.re
          (explicitFormulaFamilyHorizontalResidueWindowError
            (convolutionAutocorrelation f)
            completedPrimeContourTransportFamily
            (completedPrimeContourTransportHeightSchedule_owner.height (N : ℝ))) :=
    finitePrimeHorizontalResidueShadowAt_eq_horizontalResidueWindowError_re
      completedPrimeContourTransportHeightSchedule_owner N f
  hshadowAt.trans hunfold

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
