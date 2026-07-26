import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaZeroTail.ZetaPrimeRapidPower.ZetaPrimeTwoFaceCoordinates.ZetaPrimeContourTomography.CoordinateLedger.Owner

/-!
# Schedule-parametric coordinate tail

This file owns the finite coordinate-tail bookkeeping before specializing to the
canonical completed-prime height schedule.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open Filter
open scoped Topology

namespace ZetaAdmissibleFunction

/-- The outside-window coordinate-remainder tail along a supplied height schedule. -/
noncomputable def completedPrimeContourTransportCoordinateRemainderTailAt
    (heightSchedule :
      ExplicitFormulaCofinalHeightSchedule completedPrimeContourTransportFamily)
    (N : ℕ) (f : ZetaAdmissibleFunction) : ℝ :=
  (∑ ι in ZetaPrimePowerIndex.window N,
    finitePrimeHorizontalResidueCoordinateShadow ι f) -
    finitePrimeHorizontalResidueShadowAt heightSchedule N f

/-- The boxed finite-window remainder along a supplied height schedule. -/
noncomputable def finitePrimeHorizontalResidueCoordinateShadowBoxRemainderAt
    (heightSchedule :
      ExplicitFormulaCofinalHeightSchedule completedPrimeContourTransportFamily)
    (N : ℕ) (f : ZetaAdmissibleFunction) : ℝ :=
  (∑ ι in ZetaPrimePowerIndex.box N,
    finitePrimeHorizontalResidueCoordinateShadow ι f) -
    finitePrimeHorizontalResidueShadowAt heightSchedule N f

/-- The coordinate-shadow family is supported on genuine prime-power indices, so summing it
over the raw rectangular box is the same as summing it over the genuine prime-power
window. -/
theorem finitePrimeHorizontalResidueCoordinateShadow_box_sum_eq_window_sum_at
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    (∑ ι in ZetaPrimePowerIndex.box N,
      finitePrimeHorizontalResidueCoordinateShadow ι f) =
      ∑ ι in ZetaPrimePowerIndex.window N,
        finitePrimeHorizontalResidueCoordinateShadow ι f :=
  ZetaPrimePowerIndex.sum_box_eq_sum_window_of_zero_not_isGenuine
    (fun ι : ZetaPrimePowerIndex =>
      finitePrimeHorizontalResidueCoordinateShadow ι f)
    (finitePrimeHorizontalResidueCoordinateShadow_supportedOn_genuine f)
    N

/-- The scheduled coordinate tail unfolds to the window sum minus the scheduled
horizontal residue shadow. -/
theorem completedPrimeContourTransportCoordinateRemainderTailAt_eq_window_sub_shadowAt
    (heightSchedule :
      ExplicitFormulaCofinalHeightSchedule completedPrimeContourTransportFamily)
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    completedPrimeContourTransportCoordinateRemainderTailAt heightSchedule N f =
      (∑ ι in ZetaPrimePowerIndex.window N,
        finitePrimeHorizontalResidueCoordinateShadow ι f) -
        finitePrimeHorizontalResidueShadowAt heightSchedule N f :=
  Eq.refl
    (completedPrimeContourTransportCoordinateRemainderTailAt heightSchedule N f)

/-- The scheduled box remainder unfolds to the box sum minus the scheduled
horizontal residue shadow. -/
theorem finitePrimeHorizontalResidueCoordinateShadowBoxRemainderAt_eq_box_sub_shadowAt
    (heightSchedule :
      ExplicitFormulaCofinalHeightSchedule completedPrimeContourTransportFamily)
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    finitePrimeHorizontalResidueCoordinateShadowBoxRemainderAt heightSchedule N f =
      (∑ ι in ZetaPrimePowerIndex.box N,
        finitePrimeHorizontalResidueCoordinateShadow ι f) -
        finitePrimeHorizontalResidueShadowAt heightSchedule N f :=
  Eq.refl
    (finitePrimeHorizontalResidueCoordinateShadowBoxRemainderAt heightSchedule N f)

/-- Replacing the scheduled tail window sum by the box sum gives the scheduled
box-remainder expression. -/
theorem completedPrimeContourTransportCoordinateRemainderTailAt_eq_box_sub_shadowAt
    (heightSchedule :
      ExplicitFormulaCofinalHeightSchedule completedPrimeContourTransportFamily)
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    completedPrimeContourTransportCoordinateRemainderTailAt heightSchedule N f =
      (∑ ι in ZetaPrimePowerIndex.box N,
        finitePrimeHorizontalResidueCoordinateShadow ι f) -
        finitePrimeHorizontalResidueShadowAt heightSchedule N f :=
  Eq.trans
    (completedPrimeContourTransportCoordinateRemainderTailAt_eq_window_sub_shadowAt
      heightSchedule
      N
      f)
    (congrArg
      (fun x : ℝ => x - finitePrimeHorizontalResidueShadowAt heightSchedule N f)
      (finitePrimeHorizontalResidueCoordinateShadow_box_sum_eq_window_sum_at
        N
        f).symm)

/-- Replacing the box sum by the coordinate window gives the scheduled
coordinate-remainder expression. -/
theorem finitePrimeHorizontalResidueCoordinateShadowBoxRemainderAt_eq_window_sub_shadowAt
    (heightSchedule :
      ExplicitFormulaCofinalHeightSchedule completedPrimeContourTransportFamily)
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    finitePrimeHorizontalResidueCoordinateShadowBoxRemainderAt heightSchedule N f =
      (∑ ι in ZetaPrimePowerIndex.window N,
        finitePrimeHorizontalResidueCoordinateShadow ι f) -
        finitePrimeHorizontalResidueShadowAt heightSchedule N f :=
  Eq.trans
    (finitePrimeHorizontalResidueCoordinateShadowBoxRemainderAt_eq_box_sub_shadowAt
      heightSchedule
      N
      f)
    (congrArg
      (fun x : ℝ => x - finitePrimeHorizontalResidueShadowAt heightSchedule N f)
      (finitePrimeHorizontalResidueCoordinateShadow_box_sum_eq_window_sum_at
        N
        f))

/-- The scheduled omitted coordinate tail is the supported box remainder. -/
theorem completedPrimeContourTransportCoordinateRemainderTailAt_eq_boxRemainderAt
    (heightSchedule :
      ExplicitFormulaCofinalHeightSchedule completedPrimeContourTransportFamily)
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    completedPrimeContourTransportCoordinateRemainderTailAt heightSchedule N f =
      finitePrimeHorizontalResidueCoordinateShadowBoxRemainderAt
        heightSchedule N f :=
  Eq.trans
    (completedPrimeContourTransportCoordinateRemainderTailAt_eq_box_sub_shadowAt
      heightSchedule
      N
      f)
    (finitePrimeHorizontalResidueCoordinateShadowBoxRemainderAt_eq_box_sub_shadowAt
      heightSchedule
      N
      f).symm

/-- The scheduled box remainder is the coordinate-window difference from the scheduled
horizontal residue shadow. -/
theorem finitePrimeHorizontalResidueCoordinateShadowBoxRemainderAt_eq_coordinateRemainderWindow_sub_residueShadowAt
    (heightSchedule :
      ExplicitFormulaCofinalHeightSchedule completedPrimeContourTransportFamily)
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    finitePrimeHorizontalResidueCoordinateShadowBoxRemainderAt heightSchedule N f =
      finitePrimeContourTransportCoordinateRemainderWindow N f -
        finitePrimeHorizontalResidueShadowAt heightSchedule N f :=
  Eq.trans
    (finitePrimeHorizontalResidueCoordinateShadowBoxRemainderAt_eq_window_sub_shadowAt
      heightSchedule
      N
      f)
    (congrArg
      (fun x : ℝ => x - finitePrimeHorizontalResidueShadowAt heightSchedule N f)
      (finitePrimeContourTransportCoordinateRemainderWindow_eq_coordinateShadow_sum
        N
        f).symm)

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
