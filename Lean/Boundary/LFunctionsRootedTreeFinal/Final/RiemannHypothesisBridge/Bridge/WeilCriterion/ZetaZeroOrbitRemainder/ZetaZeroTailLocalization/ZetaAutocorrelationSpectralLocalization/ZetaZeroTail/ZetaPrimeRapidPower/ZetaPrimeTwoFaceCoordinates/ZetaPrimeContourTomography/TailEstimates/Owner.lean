import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaZeroTail.ZetaPrimeRapidPower.ZetaPrimeTwoFaceCoordinates.ZetaPrimeContourTomography.TailEstimates.ScheduleGeometry

namespace Boundary
namespace LFunctions

noncomputable section

open Filter
open scoped Topology

namespace ZetaAdmissibleFunction

/-- The finite coordinate-remainder window converges to the horizontal residue shadow.

This is the upstream prime tomography convergence theorem: the analytic tail estimate is
owned at the coordinate-remainder-window level, before box support bookkeeping or norm
packaging. -/
theorem finitePrimeHorizontalResidueCoordinateRemainderWindow_sub_residueShadow_tendsto_zero_ownerTailEstimate
    (S : CompletedPrimeContourTransportScheduledFamily)
    (f : ZetaAdmissibleFunction)
    (hPhi : ZetaPhiAnalyticControl (convolutionAutocorrelation f))
    (hLog : CompletedZetaNegLogDerivControl (convolutionAutocorrelation f)) :
    Tendsto
      (fun N : ℕ =>
        finitePrimeContourTransportCoordinateRemainderWindow N f -
          finitePrimeHorizontalResidueShadow N f)
      atTop
      (𝓝 0) := by
  have hwindow :
      Tendsto
        (fun N : ℕ => finitePrimeContourTransportCoordinateRemainderWindow N f)
        atTop
        (𝓝 0) :=
    finitePrimeContourTransportCoordinateRemainderWindow_tendsto_zero_ownerTailEstimate
      f
      (completedFiniteWindowPrimeDistributionReconstruction_of_scheduledContourFamily
        S f)
  have hshadow :
      Tendsto
        (fun N : ℕ => finitePrimeHorizontalResidueShadow N f)
        atTop
        (𝓝 0) := by
    exact
      finitePrimeHorizontalResidueShadow_tendsto_zero_ownerTailEstimate
        S.toScheduleGeometry
        f
        hPhi
        hLog
  have hsub :
      Tendsto
        (fun N : ℕ =>
          finitePrimeContourTransportCoordinateRemainderWindow N f -
            finitePrimeHorizontalResidueShadow N f)
        atTop
        (𝓝 (0 - 0)) :=
    hwindow.sub hshadow
  exact Eq.subst
    (motive := fun x : ℝ =>
      Tendsto
        (fun N : ℕ =>
          finitePrimeContourTransportCoordinateRemainderWindow N f -
            finitePrimeHorizontalResidueShadow N f)
        atTop
        (𝓝 x))
    (sub_zero 0)
    hsub

/-- The finite tomographic residual is bounded by the supported boxed remainder.

This is the pointwise remainder-bound layer after support reduction: the residual error is
identified with the boxed coordinate-shadow remainder, then bounded by its unfolded norm. -/
theorem finitePrimeContourTransportTomographicError_remainderBound
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    ‖finitePrimeContourTransportTomographicError N f‖ ≤
      ‖(∑ ι in ZetaPrimePowerIndex.box N,
          finitePrimeHorizontalResidueCoordinateShadow ι f) -
        finitePrimeHorizontalResidueShadow N f‖ := by
  calc
    ‖finitePrimeContourTransportTomographicError N f‖ =
        ‖finitePrimeHorizontalResidueCoordinateShadowBoxRemainder N f‖ := by
      exact congrArg norm
        (finitePrimeHorizontalResidueCoordinateShadowBoxRemainder_eq_tomographicError
          N f).symm
    _ ≤
        ‖(∑ ι in ZetaPrimePowerIndex.box N,
            finitePrimeHorizontalResidueCoordinateShadow ι f) -
          finitePrimeHorizontalResidueShadow N f‖ := by
      exact finitePrimeHorizontalResidueCoordinateShadowBoxRemainder_norm_bound
        N f

/-- The explicit finite-window tail majorant for the tomographic residual.

This is the norm of the supported boxed coordinate-shadow remainder against the horizontal
residue shadow. -/
noncomputable def finitePrimeContourTransportTomographicErrorRemainderMajorant
    (N : ℕ) (f : ZetaAdmissibleFunction) : ℝ :=
  ‖(∑ ι in ZetaPrimePowerIndex.box N,
      finitePrimeHorizontalResidueCoordinateShadow ι f) -
    finitePrimeHorizontalResidueShadow N f‖

/-- The finite tomographic residual norm is the explicit boxed-remainder majorant. -/
theorem finitePrimeContourTransportTomographicError_norm_eq_remainderMajorant
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    ‖finitePrimeContourTransportTomographicError N f‖ =
      finitePrimeContourTransportTomographicErrorRemainderMajorant N f := by
  calc
    ‖finitePrimeContourTransportTomographicError N f‖ =
        ‖finitePrimeHorizontalResidueCoordinateShadowBoxRemainder N f‖ := by
      exact congrArg norm
        (finitePrimeHorizontalResidueCoordinateShadowBoxRemainder_eq_tomographicError
          N f).symm
    _ =
        ‖(∑ ι in ZetaPrimePowerIndex.box N,
            finitePrimeHorizontalResidueCoordinateShadow ι f) -
          finitePrimeHorizontalResidueShadow N f‖ := by
      exact congrArg norm
        (finitePrimeHorizontalResidueCoordinateShadowBoxRemainder_eq N f)
    _ = finitePrimeContourTransportTomographicErrorRemainderMajorant N f := by
      rfl

/-- The boxed coordinate-shadow remainder has norm tending to zero.

This is the exact tail-localization estimate behind the finite tomographic majorant: after
support reduction, the only omitted term is the boxed coordinate-shadow remainder against
the horizontal residue shadow. -/
theorem finitePrimeHorizontalResidueCoordinateShadowBoxRemainder_norm_tendsto_zero_ownerTailEstimate
    (S : CompletedPrimeContourTransportScheduledFamily)
    (f : ZetaAdmissibleFunction)
    (hPhi : ZetaPhiAnalyticControl (convolutionAutocorrelation f))
    (hLog : CompletedZetaNegLogDerivControl (convolutionAutocorrelation f)) :
    Tendsto
      (fun N : ℕ => ‖finitePrimeHorizontalResidueCoordinateShadowBoxRemainder N f‖)
      atTop
      (𝓝 0) := by
  have hwindow :
      Tendsto
        (fun N : ℕ =>
          finitePrimeContourTransportCoordinateRemainderWindow N f -
            finitePrimeHorizontalResidueShadow N f)
        atTop
        (𝓝 0) :=
    finitePrimeHorizontalResidueCoordinateRemainderWindow_sub_residueShadow_tendsto_zero_ownerTailEstimate
      S
      f
      hPhi
      hLog
  have hnorm :
      Tendsto
        (fun N : ℕ =>
          ‖finitePrimeContourTransportCoordinateRemainderWindow N f -
            finitePrimeHorizontalResidueShadow N f‖)
        atTop
        (𝓝 ‖(0 : ℝ)‖) :=
    hwindow.norm
  have hfun :
      (fun N : ℕ => ‖finitePrimeHorizontalResidueCoordinateShadowBoxRemainder N f‖) =
        (fun N : ℕ =>
          ‖finitePrimeContourTransportCoordinateRemainderWindow N f -
            finitePrimeHorizontalResidueShadow N f‖) := by
    funext N
    exact congrArg norm
      (finitePrimeHorizontalResidueCoordinateShadowBoxRemainder_eq_coordinateRemainderWindow_sub_residueShadow
        N f)
  exact Eq.subst
    (motive := fun u : ℕ → ℝ => Tendsto u atTop (𝓝 0))
    hfun.symm
    (Eq.subst
      (motive := fun x : ℝ =>
        Tendsto
          (fun N : ℕ =>
            ‖finitePrimeContourTransportCoordinateRemainderWindow N f -
              finitePrimeHorizontalResidueShadow N f‖)
          atTop
          (𝓝 x))
      (norm_zero : ‖(0 : ℝ)‖ = 0)
      hnorm)


end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
