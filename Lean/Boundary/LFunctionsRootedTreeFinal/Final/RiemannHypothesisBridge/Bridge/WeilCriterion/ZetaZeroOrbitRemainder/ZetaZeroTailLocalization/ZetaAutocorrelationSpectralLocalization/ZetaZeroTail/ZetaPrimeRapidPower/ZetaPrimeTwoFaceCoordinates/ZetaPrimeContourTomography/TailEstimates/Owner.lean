import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaZeroTail.ZetaPrimeRapidPower.ZetaPrimeTwoFaceCoordinates.ZetaPrimeContourTomography.TailEstimates.ScheduleGeometry
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaZeroTail.ZetaPrimeRapidPower.ZetaPrimeTwoFaceCoordinates.ZetaPrimeContourTomography.TailEstimates.CoordinateTail
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaZeroTail.ZetaPrimeRapidPower.ZetaPrimeTwoFaceCoordinates.ZetaPrimeContourTomography.TailEstimates.CoordinateTailAt

namespace Boundary
namespace LFunctions

noncomputable section

open Filter
open scoped Topology

namespace ZetaAdmissibleFunction

/-- The finite coordinate-remainder window converges to the horizontal residue shadow.

This is the upstream prime tomography convergence theorem: the analytic tail estimate is
owned at the coordinate-remainder-window level, before choosing a concrete height schedule
or applying box support bookkeeping. -/
theorem finitePrimeHorizontalResidueCoordinateRemainderWindow_sub_residueShadowAt_tendsto_zero_ownerTailEstimate
    (S : CompletedPrimeContourTransportScheduledFamily)
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
          finitePrimeHorizontalResidueShadowAt S.height_schedule N f)
      atTop
      (𝓝 0) :=
  let hwindow :
      Tendsto
        (fun N : ℕ => finitePrimeContourTransportCoordinateRemainderWindow N f)
        atTop
        (𝓝 0) :=
    finitePrimeContourTransportCoordinateRemainderWindow_tendsto_zero_of_summedTransport
      f
      (completedSummedPrimeContourTimeTransport_of_scheduledContourFamily
        S f)
  let hshadow :
      Tendsto
        (fun N : ℕ => finitePrimeHorizontalResidueShadowAt S.height_schedule N f)
        atTop
        (𝓝 0) :=
    finitePrimeHorizontalResidueShadowAt_tendsto_zero_of_scheduledPackage
      S.toScheduleGeometry
      f
      hPhi
      hHorizontal
  let hsub :
      Tendsto
        (fun N : ℕ =>
          finitePrimeContourTransportCoordinateRemainderWindow N f -
            finitePrimeHorizontalResidueShadowAt S.height_schedule N f)
        atTop
        (𝓝 (0 - 0)) :=
    hwindow.sub hshadow
  Eq.subst
    (motive := fun x : ℝ =>
      Tendsto
        (fun N : ℕ =>
          finitePrimeContourTransportCoordinateRemainderWindow N f -
            finitePrimeHorizontalResidueShadowAt S.height_schedule N f)
        atTop
        (𝓝 x))
    (sub_zero 0)
    hsub

/-- The explicit finite-window tail majorant for the tomographic residual.

This is the norm of the supported boxed coordinate-shadow remainder against the horizontal
residue shadow. -/
noncomputable def finitePrimeContourTransportTomographicErrorRemainderMajorantAt
    (heightSchedule :
      ExplicitFormulaCofinalHeightSchedule completedPrimeContourTransportFamily)
    (N : ℕ) (f : ZetaAdmissibleFunction) : ℝ :=
  ‖(∑ ι in ZetaPrimePowerIndex.box N,
      finitePrimeHorizontalResidueCoordinateShadow ι f) -
    finitePrimeHorizontalResidueShadowAt heightSchedule N f‖

/-- The scheduled boxed coordinate-shadow remainder norm is the scheduled finite-window
tail majorant. -/
theorem finitePrimeHorizontalResidueCoordinateShadowBoxRemainderAt_norm_eq_remainderMajorantAt
    (heightSchedule :
      ExplicitFormulaCofinalHeightSchedule completedPrimeContourTransportFamily)
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    ‖finitePrimeHorizontalResidueCoordinateShadowBoxRemainderAt
        heightSchedule N f‖ =
      finitePrimeContourTransportTomographicErrorRemainderMajorantAt
        heightSchedule N f :=
  Eq.refl
    ‖finitePrimeHorizontalResidueCoordinateShadowBoxRemainderAt
      heightSchedule N f‖

/-- The scheduled explicit finite-window tail majorant tends to zero. -/
theorem finitePrimeContourTransportTomographicErrorRemainderMajorantAt_tendsto_zero
    (S : CompletedPrimeContourTransportScheduledFamily)
    (f : ZetaAdmissibleFunction)
    (hPhi : ZetaPhiAnalyticControl (convolutionAutocorrelation f))
    (hHorizontal :
      ExplicitFormulaScheduledHorizontalLogDerivControl
        (convolutionAutocorrelation f)
        completedPrimeContourTransportFamily
        S.height_schedule) :
    Tendsto
      (fun N : ℕ =>
        finitePrimeContourTransportTomographicErrorRemainderMajorantAt
          S.height_schedule N f)
      atTop
      (𝓝 0) :=
  let hbox :
      Tendsto
        (fun N : ℕ =>
          ‖finitePrimeContourTransportCoordinateRemainderWindow N f -
            finitePrimeHorizontalResidueShadowAt S.height_schedule N f‖)
        atTop
        (𝓝 ‖(0 : ℝ)‖) :=
    (finitePrimeHorizontalResidueCoordinateRemainderWindow_sub_residueShadowAt_tendsto_zero_ownerTailEstimate
      S
      f
      hPhi
      hHorizontal).norm
  let hzero : ‖(0 : ℝ)‖ = 0 :=
    norm_zero
  let hfun :
      (fun N : ℕ =>
        ‖finitePrimeContourTransportCoordinateRemainderWindow N f -
          finitePrimeHorizontalResidueShadowAt S.height_schedule N f‖) =
        (fun N : ℕ =>
          finitePrimeContourTransportTomographicErrorRemainderMajorantAt
            S.height_schedule N f) :=
    funext
      (fun N : ℕ =>
        let hcoordinate :
            finitePrimeHorizontalResidueCoordinateShadowBoxRemainderAt
                S.height_schedule N f =
              finitePrimeContourTransportCoordinateRemainderWindow N f -
                finitePrimeHorizontalResidueShadowAt S.height_schedule N f :=
          finitePrimeHorizontalResidueCoordinateShadowBoxRemainderAt_eq_coordinateRemainderWindow_sub_residueShadowAt
            S.height_schedule N f
        let hnormCoordinate :
            ‖finitePrimeContourTransportCoordinateRemainderWindow N f -
              finitePrimeHorizontalResidueShadowAt S.height_schedule N f‖ =
              ‖finitePrimeHorizontalResidueCoordinateShadowBoxRemainderAt
                S.height_schedule N f‖ :=
          congrArg norm hcoordinate.symm
        let hmajorant :
            ‖finitePrimeHorizontalResidueCoordinateShadowBoxRemainderAt
                S.height_schedule N f‖ =
              finitePrimeContourTransportTomographicErrorRemainderMajorantAt
                S.height_schedule N f :=
          finitePrimeHorizontalResidueCoordinateShadowBoxRemainderAt_norm_eq_remainderMajorantAt
            S.height_schedule N f
        hnormCoordinate.trans hmajorant)
  Eq.subst
    (motive := fun u : ℕ → ℝ => Tendsto u atTop (𝓝 0))
    hfun
    (Eq.subst
      (motive := fun x : ℝ =>
        Tendsto
          (fun N : ℕ =>
            ‖finitePrimeContourTransportCoordinateRemainderWindow N f -
              finitePrimeHorizontalResidueShadowAt S.height_schedule N f‖)
          atTop
          (𝓝 x))
      hzero
      hbox)

/-- The boxed coordinate-shadow remainder has norm tending to zero.

This is the exact tail-localization estimate behind the finite tomographic majorant: after
support reduction, the only omitted term is the boxed coordinate-shadow remainder against
the scheduled horizontal residue shadow. -/
theorem finitePrimeHorizontalResidueCoordinateShadowBoxRemainderAt_norm_tendsto_zero_ownerTailEstimate
    (S : CompletedPrimeContourTransportScheduledFamily)
    (f : ZetaAdmissibleFunction)
    (hPhi : ZetaPhiAnalyticControl (convolutionAutocorrelation f))
    (hHorizontal :
      ExplicitFormulaScheduledHorizontalLogDerivControl
        (convolutionAutocorrelation f)
        completedPrimeContourTransportFamily
        S.height_schedule) :
    Tendsto
      (fun N : ℕ =>
        ‖finitePrimeHorizontalResidueCoordinateShadowBoxRemainderAt
          S.height_schedule N f‖)
      atTop
      (𝓝 0) :=
  let hwindow :
      Tendsto
        (fun N : ℕ =>
          finitePrimeContourTransportCoordinateRemainderWindow N f -
            finitePrimeHorizontalResidueShadowAt S.height_schedule N f)
        atTop
        (𝓝 0) :=
    finitePrimeHorizontalResidueCoordinateRemainderWindow_sub_residueShadowAt_tendsto_zero_ownerTailEstimate
      S
      f
      hPhi
      hHorizontal
  let hnorm :
      Tendsto
        (fun N : ℕ =>
          ‖finitePrimeContourTransportCoordinateRemainderWindow N f -
            finitePrimeHorizontalResidueShadowAt S.height_schedule N f‖)
        atTop
        (𝓝 ‖(0 : ℝ)‖) :=
    hwindow.norm
  let hfun :
      (fun N : ℕ =>
        ‖finitePrimeHorizontalResidueCoordinateShadowBoxRemainderAt
          S.height_schedule N f‖) =
        (fun N : ℕ =>
          ‖finitePrimeContourTransportCoordinateRemainderWindow N f -
            finitePrimeHorizontalResidueShadowAt S.height_schedule N f‖) :=
    funext
      (fun N : ℕ =>
        congrArg norm
      (finitePrimeHorizontalResidueCoordinateShadowBoxRemainderAt_eq_coordinateRemainderWindow_sub_residueShadowAt
        S.height_schedule N f))
  Eq.subst
    (motive := fun u : ℕ → ℝ => Tendsto u atTop (𝓝 0))
    hfun.symm
    (Eq.subst
      (motive := fun x : ℝ =>
        Tendsto
          (fun N : ℕ =>
            ‖finitePrimeContourTransportCoordinateRemainderWindow N f -
              finitePrimeHorizontalResidueShadowAt S.height_schedule N f‖)
          atTop
          (𝓝 x))
      (norm_zero : ‖(0 : ℝ)‖ = 0)
      hnorm)

/-- The scheduled boxed coordinate-shadow remainder tends to zero. -/
theorem finitePrimeHorizontalResidueCoordinateShadowBoxRemainderAt_tendsto_zero_ownerTailEstimate
    (S : CompletedPrimeContourTransportScheduledFamily)
    (f : ZetaAdmissibleFunction)
    (hPhi : ZetaPhiAnalyticControl (convolutionAutocorrelation f))
    (hHorizontal :
      ExplicitFormulaScheduledHorizontalLogDerivControl
        (convolutionAutocorrelation f)
        completedPrimeContourTransportFamily
        S.height_schedule) :
    Tendsto
      (fun N : ℕ =>
        finitePrimeHorizontalResidueCoordinateShadowBoxRemainderAt
          S.height_schedule N f)
      atTop
      (𝓝 0) :=
  let hnorm :
      Tendsto
        (fun N : ℕ =>
          ‖finitePrimeHorizontalResidueCoordinateShadowBoxRemainderAt
            S.height_schedule N f‖)
        atTop
        (𝓝 0) :=
    finitePrimeHorizontalResidueCoordinateShadowBoxRemainderAt_norm_tendsto_zero_ownerTailEstimate
      S
      f
      hPhi
      hHorizontal
  let hbound :
      ∀ᶠ N in atTop,
        ‖finitePrimeHorizontalResidueCoordinateShadowBoxRemainderAt
          S.height_schedule N f‖ ≤
          ‖finitePrimeHorizontalResidueCoordinateShadowBoxRemainderAt
            S.height_schedule N f‖ :=
    Eventually.of_forall (fun N : ℕ => le_rfl)
  squeeze_zero_norm' hbound hnorm

/-- The scheduled coordinate-remainder tail tends to zero. -/
theorem completedPrimeContourTransportCoordinateRemainderTailAt_tendsto_zero_ownerTailEstimate
    (S : CompletedPrimeContourTransportScheduledFamily)
    (f : ZetaAdmissibleFunction)
    (hPhi : ZetaPhiAnalyticControl (convolutionAutocorrelation f))
    (hHorizontal :
      ExplicitFormulaScheduledHorizontalLogDerivControl
        (convolutionAutocorrelation f)
        completedPrimeContourTransportFamily
        S.height_schedule) :
    Tendsto
      (fun N : ℕ =>
        completedPrimeContourTransportCoordinateRemainderTailAt
          S.height_schedule N f)
      atTop
      (𝓝 0) :=
  let hbox :
      Tendsto
        (fun N : ℕ =>
          finitePrimeHorizontalResidueCoordinateShadowBoxRemainderAt
            S.height_schedule N f)
        atTop
        (𝓝 0) :=
    finitePrimeHorizontalResidueCoordinateShadowBoxRemainderAt_tendsto_zero_ownerTailEstimate
      S
      f
      hPhi
      hHorizontal
  let hfun :
      (fun N : ℕ =>
        completedPrimeContourTransportCoordinateRemainderTailAt
          S.height_schedule N f) =
        (fun N : ℕ =>
          finitePrimeHorizontalResidueCoordinateShadowBoxRemainderAt
            S.height_schedule N f) :=
    funext
      (fun N : ℕ =>
        completedPrimeContourTransportCoordinateRemainderTailAt_eq_boxRemainderAt
          S.height_schedule N f)
  Eq.subst
    (motive := fun u : ℕ → ℝ => Tendsto u atTop (𝓝 0))
    hfun.symm
    hbox

/-- The finite coordinate-shadow window and scheduled horizontal residue shadow differ by
a term tending to zero. -/
theorem finitePrimeHorizontalResidueCoordinateShadow_window_sub_residueShadowAt_tendsto_zero
    (S : CompletedPrimeContourTransportScheduledFamily)
    (f : ZetaAdmissibleFunction)
    (hPhi : ZetaPhiAnalyticControl (convolutionAutocorrelation f))
    (hHorizontal :
      ExplicitFormulaScheduledHorizontalLogDerivControl
        (convolutionAutocorrelation f)
        completedPrimeContourTransportFamily
        S.height_schedule) :
    Tendsto
      (fun N : ℕ =>
        (∑ ι in ZetaPrimePowerIndex.window N,
          finitePrimeHorizontalResidueCoordinateShadow ι f) -
          finitePrimeHorizontalResidueShadowAt S.height_schedule N f)
      atTop
      (𝓝 0) :=
  let htail :
      Tendsto
        (fun N : ℕ =>
          completedPrimeContourTransportCoordinateRemainderTailAt
            S.height_schedule N f)
        atTop
        (𝓝 0) :=
    completedPrimeContourTransportCoordinateRemainderTailAt_tendsto_zero_ownerTailEstimate
      S
      f
      hPhi
      hHorizontal
  let hfun :
      (fun N : ℕ =>
        (∑ ι in ZetaPrimePowerIndex.window N,
          finitePrimeHorizontalResidueCoordinateShadow ι f) -
          finitePrimeHorizontalResidueShadowAt S.height_schedule N f) =
        (fun N : ℕ =>
          completedPrimeContourTransportCoordinateRemainderTailAt
            S.height_schedule N f) :=
    funext
      (fun N : ℕ =>
        Eq.refl
          ((∑ ι in ZetaPrimePowerIndex.window N,
            finitePrimeHorizontalResidueCoordinateShadow ι f) -
            finitePrimeHorizontalResidueShadowAt S.height_schedule N f))
  Eq.subst
    (motive := fun u : ℕ → ℝ => Tendsto u atTop (𝓝 0))
    hfun.symm
    htail

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
