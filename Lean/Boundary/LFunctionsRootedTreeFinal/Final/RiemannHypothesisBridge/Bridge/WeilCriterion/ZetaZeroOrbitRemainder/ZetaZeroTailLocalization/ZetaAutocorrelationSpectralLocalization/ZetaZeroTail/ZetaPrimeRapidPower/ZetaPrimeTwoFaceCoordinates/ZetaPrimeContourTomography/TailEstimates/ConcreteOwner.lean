import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaZeroTail.ZetaPrimeRapidPower.ZetaPrimeTwoFaceCoordinates.ZetaPrimeContourTomography.TailEstimates.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaZeroTail.ZetaPrimeRapidPower.ZetaPrimeTwoFaceCoordinates.ZetaPrimeContourTomography.TailEstimates.ScheduleGeometryConcrete
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaZeroTail.ZetaPrimeRapidPower.ZetaPrimeTwoFaceCoordinates.ZetaPrimeContourTomography.TailEstimates.CoordinateTail

/-!
# Concrete tail estimates

This file owns the canonical-height specializations of the schedule-parametric
tail estimates in `TailEstimates.Owner`.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open Filter
open scoped Topology

namespace ZetaAdmissibleFunction

/-- The scheduled residue shadow specializes to the concrete owner schedule. -/
theorem finitePrimeHorizontalResidueShadowAt_eq_shadow_ownerSchedule
    (S : CompletedPrimeContourTransportScheduledFamily)
    (hheight :
      S.height_schedule = completedPrimeContourTransportHeightSchedule_owner)
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    finitePrimeHorizontalResidueShadowAt S.height_schedule N f =
      finitePrimeHorizontalResidueShadow N f :=
  Eq.trans
    (congrArg
      (fun heightSchedule :
        ExplicitFormulaCofinalHeightSchedule completedPrimeContourTransportFamily =>
        finitePrimeHorizontalResidueShadowAt heightSchedule N f)
      hheight)
    (finitePrimeHorizontalResidueShadow_eq_shadowAt_ownerSchedule N f).symm

/-- Pointwise coordinate-remainder transport from the scheduled shadow to the
concrete owner shadow. -/
theorem finitePrimeHorizontalResidueCoordinateRemainderWindow_sub_shadowAt_eq_sub_shadow
    (S : CompletedPrimeContourTransportScheduledFamily)
    (hheight :
      S.height_schedule = completedPrimeContourTransportHeightSchedule_owner)
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    finitePrimeContourTransportCoordinateRemainderWindow N f -
        finitePrimeHorizontalResidueShadowAt S.height_schedule N f =
      finitePrimeContourTransportCoordinateRemainderWindow N f -
        finitePrimeHorizontalResidueShadow N f :=
  congrArg
    (fun x : ℝ => finitePrimeContourTransportCoordinateRemainderWindow N f - x)
    (finitePrimeHorizontalResidueShadowAt_eq_shadow_ownerSchedule
      S
      hheight
      N
      f)

/-- Function-level coordinate-remainder transport from scheduled to concrete
owner shadows. -/
theorem finitePrimeHorizontalResidueCoordinateRemainderWindow_sub_shadowAt_fun_eq_sub_shadow
    (S : CompletedPrimeContourTransportScheduledFamily)
    (hheight :
      S.height_schedule = completedPrimeContourTransportHeightSchedule_owner)
    (f : ZetaAdmissibleFunction) :
    (fun N : ℕ =>
      finitePrimeContourTransportCoordinateRemainderWindow N f -
        finitePrimeHorizontalResidueShadowAt S.height_schedule N f) =
      (fun N : ℕ =>
        finitePrimeContourTransportCoordinateRemainderWindow N f -
          finitePrimeHorizontalResidueShadow N f) :=
  funext
    (fun N =>
      finitePrimeHorizontalResidueCoordinateRemainderWindow_sub_shadowAt_eq_sub_shadow
        S
        hheight
        N
        f)

/-- Concrete-wrapper form of the coordinate-remainder window convergence. -/
theorem finitePrimeHorizontalResidueCoordinateRemainderWindow_sub_residueShadow_tendsto_zero_ownerTailEstimate
    (S : CompletedPrimeContourTransportScheduledFamily)
    (hheight :
      S.height_schedule = completedPrimeContourTransportHeightSchedule_owner)
    (f : ZetaAdmissibleFunction)
    (hPhi : ZetaPhiAnalyticControl (convolutionAutocorrelation f))
    (hHorizontal :
      ExplicitFormulaScheduledHorizontalLogDerivControl
        (convolutionAutocorrelation f)
        completedPrimeContourTransportFamily
        S.height_schedule) :
    Tendsto
      (fun N : ℕ =>
        finitePrimeContourTransportCoordinateRemainderWindow N f -
          finitePrimeHorizontalResidueShadow N f)
      atTop
      (𝓝 0) :=
  Eq.subst
    (motive := fun u : ℕ → ℝ => Tendsto u atTop (𝓝 0))
    (finitePrimeHorizontalResidueCoordinateRemainderWindow_sub_shadowAt_fun_eq_sub_shadow
      S
      hheight
      f)
    (finitePrimeHorizontalResidueCoordinateRemainderWindow_sub_residueShadowAt_tendsto_zero_ownerTailEstimate
      S
      f
      hPhi
      hHorizontal)

/-- The finite tomographic residual norm equals the boxed coordinate-shadow
remainder norm. -/
theorem finitePrimeContourTransportTomographicError_norm_eq_shadowBoxRemainder_norm
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    ‖finitePrimeContourTransportTomographicError N f‖ =
      ‖finitePrimeHorizontalResidueCoordinateShadowBoxRemainder N f‖ :=
  congrArg
    norm
    (finitePrimeHorizontalResidueCoordinateShadowBoxRemainder_eq_tomographicError
      N
      f).symm

/-- The boxed coordinate-shadow remainder norm equals the explicit shadow
sum remainder norm. -/
theorem finitePrimeHorizontalResidueCoordinateShadowBoxRemainder_norm_eq_sum_shadow_norm
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    ‖finitePrimeHorizontalResidueCoordinateShadowBoxRemainder N f‖ =
      ‖(∑ ι in ZetaPrimePowerIndex.box N,
          finitePrimeHorizontalResidueCoordinateShadow ι f) -
        finitePrimeHorizontalResidueShadow N f‖ :=
  congrArg
    norm
    (finitePrimeHorizontalResidueCoordinateShadowBoxRemainder_eq N f)

/-- The tomographic residual norm is bounded by the explicit shadow sum
remainder norm after the residual/box identification. -/
theorem finitePrimeContourTransportTomographicError_norm_le_sum_shadow_norm
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    ‖finitePrimeContourTransportTomographicError N f‖ ≤
      ‖(∑ ι in ZetaPrimePowerIndex.box N,
          finitePrimeHorizontalResidueCoordinateShadow ι f) -
        finitePrimeHorizontalResidueShadow N f‖ :=
  Eq.subst
    (motive := fun x : ℝ =>
      x ≤
        ‖(∑ ι in ZetaPrimePowerIndex.box N,
            finitePrimeHorizontalResidueCoordinateShadow ι f) -
          finitePrimeHorizontalResidueShadow N f‖)
    (finitePrimeContourTransportTomographicError_norm_eq_shadowBoxRemainder_norm
      N
      f).symm
    (finitePrimeHorizontalResidueCoordinateShadowBoxRemainder_norm_bound
      N
      f)

/-- The tomographic residual norm is the explicit boxed-remainder majorant,
with the definition unfolded at the final equality. -/
theorem finitePrimeContourTransportTomographicError_norm_eq_remainderMajorant_core
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    ‖finitePrimeContourTransportTomographicError N f‖ =
      ‖(∑ ι in ZetaPrimePowerIndex.box N,
          finitePrimeHorizontalResidueCoordinateShadow ι f) -
        finitePrimeHorizontalResidueShadow N f‖ :=
  Eq.trans
    (finitePrimeContourTransportTomographicError_norm_eq_shadowBoxRemainder_norm
      N
      f)
    (finitePrimeHorizontalResidueCoordinateShadowBoxRemainder_norm_eq_sum_shadow_norm
      N
      f)

/-- The scheduled boxed coordinate-shadow remainder specializes to the concrete
owner schedule. -/
theorem finitePrimeHorizontalResidueCoordinateShadowBoxRemainderAt_eq_concrete
    (S : CompletedPrimeContourTransportScheduledFamily)
    (hheight :
      S.height_schedule = completedPrimeContourTransportHeightSchedule_owner)
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    finitePrimeHorizontalResidueCoordinateShadowBoxRemainderAt
        S.height_schedule N f =
      finitePrimeHorizontalResidueCoordinateShadowBoxRemainder N f :=
  Eq.trans
    (congrArg
      (fun heightSchedule :
        ExplicitFormulaCofinalHeightSchedule completedPrimeContourTransportFamily =>
        finitePrimeHorizontalResidueCoordinateShadowBoxRemainderAt
          heightSchedule N f)
      hheight)
    (Eq.refl
      (finitePrimeHorizontalResidueCoordinateShadowBoxRemainder N f))

/-- Pointwise norm transport for the boxed coordinate-shadow remainder. -/
theorem finitePrimeHorizontalResidueCoordinateShadowBoxRemainderAt_norm_eq_concrete_norm
    (S : CompletedPrimeContourTransportScheduledFamily)
    (hheight :
      S.height_schedule = completedPrimeContourTransportHeightSchedule_owner)
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    ‖finitePrimeHorizontalResidueCoordinateShadowBoxRemainderAt
        S.height_schedule N f‖ =
      ‖finitePrimeHorizontalResidueCoordinateShadowBoxRemainder N f‖ :=
  congrArg
    norm
    (finitePrimeHorizontalResidueCoordinateShadowBoxRemainderAt_eq_concrete
      S
      hheight
      N
      f)

/-- Function-level norm transport for the boxed coordinate-shadow remainder. -/
theorem finitePrimeHorizontalResidueCoordinateShadowBoxRemainderAt_norm_fun_eq_concrete_norm
    (S : CompletedPrimeContourTransportScheduledFamily)
    (hheight :
      S.height_schedule = completedPrimeContourTransportHeightSchedule_owner)
    (f : ZetaAdmissibleFunction) :
    (fun N : ℕ =>
      ‖finitePrimeHorizontalResidueCoordinateShadowBoxRemainderAt
        S.height_schedule N f‖) =
      (fun N : ℕ =>
        ‖finitePrimeHorizontalResidueCoordinateShadowBoxRemainder N f‖) :=
  funext
    (fun N =>
      finitePrimeHorizontalResidueCoordinateShadowBoxRemainderAt_norm_eq_concrete_norm
        S
        hheight
        N
        f)

/-- The finite coordinate-remainder window converges to the horizontal residue shadow
from concrete separated factor bounds on the scheduled carrier. -/
theorem finitePrimeHorizontalResidueCoordinateRemainderWindow_sub_residueShadow_tendsto_zero_of_concreteFactorData
    (S : CompletedPrimeContourTransportScheduledFamily)
    (hheight :
      S.height_schedule = completedPrimeContourTransportHeightSchedule_owner)
    (f : ZetaAdmissibleFunction)
    (hPhi : ZetaPhiAnalyticControl (convolutionAutocorrelation f))
    (D :
      CompletedPrimeContourTransportConcreteFactorData
        S.toScheduleGeometry) :
    Tendsto
      (fun N : ℕ =>
        finitePrimeContourTransportCoordinateRemainderWindow N f -
          finitePrimeHorizontalResidueShadow N f)
      atTop
      (𝓝 0) :=
  finitePrimeHorizontalResidueCoordinateRemainderWindow_sub_residueShadow_tendsto_zero_ownerTailEstimate
    S
    hheight
    f
    hPhi
    (D.toScheduledHorizontalLogDerivControl f)

/-- The finite tomographic residual is bounded by the supported boxed remainder. -/
theorem finitePrimeContourTransportTomographicError_remainderBound
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    ‖finitePrimeContourTransportTomographicError N f‖ ≤
      ‖(∑ ι in ZetaPrimePowerIndex.box N,
          finitePrimeHorizontalResidueCoordinateShadow ι f) -
        finitePrimeHorizontalResidueShadow N f‖ :=
  finitePrimeContourTransportTomographicError_norm_le_sum_shadow_norm
    N
    f

/-- The concrete explicit finite-window tail majorant for the tomographic residual. -/
noncomputable def finitePrimeContourTransportTomographicErrorRemainderMajorant
    (N : ℕ) (f : ZetaAdmissibleFunction) : ℝ :=
  ‖(∑ ι in ZetaPrimePowerIndex.box N,
      finitePrimeHorizontalResidueCoordinateShadow ι f) -
    finitePrimeHorizontalResidueShadow N f‖

/-- The finite tomographic residual norm is the explicit boxed-remainder majorant. -/
theorem finitePrimeContourTransportTomographicError_norm_eq_remainderMajorant
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    ‖finitePrimeContourTransportTomographicError N f‖ =
      finitePrimeContourTransportTomographicErrorRemainderMajorant N f :=
  finitePrimeContourTransportTomographicError_norm_eq_remainderMajorant_core
    N
    f

/-- The concrete boxed coordinate-shadow remainder has norm tending to zero. -/
theorem finitePrimeHorizontalResidueCoordinateShadowBoxRemainder_norm_tendsto_zero_ownerTailEstimate
    (S : CompletedPrimeContourTransportScheduledFamily)
    (hheight :
      S.height_schedule = completedPrimeContourTransportHeightSchedule_owner)
    (f : ZetaAdmissibleFunction)
    (hPhi : ZetaPhiAnalyticControl (convolutionAutocorrelation f))
    (hHorizontal :
      ExplicitFormulaScheduledHorizontalLogDerivControl
        (convolutionAutocorrelation f)
        completedPrimeContourTransportFamily
        S.height_schedule) :
    Tendsto
      (fun N : ℕ => ‖finitePrimeHorizontalResidueCoordinateShadowBoxRemainder N f‖)
      atTop
      (𝓝 0) :=
  Eq.subst
    (motive := fun u : ℕ → ℝ => Tendsto u atTop (𝓝 0))
    (finitePrimeHorizontalResidueCoordinateShadowBoxRemainderAt_norm_fun_eq_concrete_norm
      S
      hheight
      f)
    (finitePrimeHorizontalResidueCoordinateShadowBoxRemainderAt_norm_tendsto_zero_ownerTailEstimate
      S
      f
      hPhi
      hHorizontal)

/-- The boxed coordinate-shadow remainder has norm tending to zero from concrete
separated factor bounds on the scheduled carrier. -/
theorem finitePrimeHorizontalResidueCoordinateShadowBoxRemainder_norm_tendsto_zero_of_concreteFactorData
    (S : CompletedPrimeContourTransportScheduledFamily)
    (hheight :
      S.height_schedule = completedPrimeContourTransportHeightSchedule_owner)
    (f : ZetaAdmissibleFunction)
    (hPhi : ZetaPhiAnalyticControl (convolutionAutocorrelation f))
    (D :
      CompletedPrimeContourTransportConcreteFactorData
        S.toScheduleGeometry) :
    Tendsto
      (fun N : ℕ => ‖finitePrimeHorizontalResidueCoordinateShadowBoxRemainder N f‖)
      atTop
      (𝓝 0) :=
  finitePrimeHorizontalResidueCoordinateShadowBoxRemainder_norm_tendsto_zero_ownerTailEstimate
    S
    hheight
    f
    hPhi
    (D.toScheduledHorizontalLogDerivControl f)

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
