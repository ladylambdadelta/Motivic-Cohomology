import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaZeroTail.ZetaPrimeRapidPower.ZetaPrimeTwoFaceCoordinates.ZetaPrimeContourTomography.GNSNormalization.TomographicMajorant
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaZeroTail.ZetaPrimeRapidPower.ZetaPrimeTwoFaceCoordinates.ZetaPrimeContourTomography.GNSNormalization.ParametricTail

/-!
# Prime contour tomography

This owner layer is split from the public tomography owner.  It preserves the
public theorem names while keeping the proof graph in smaller linear layers.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open Filter
open scoped Topology

namespace ZetaAdmissibleFunction

/-- Norm convergence of the finite tomographic residual remainder.

This is the remaining analytic tail estimate after support reduction and the pointwise
remainder bound: the finite tomographic residual has norm tending to zero. -/
theorem finitePrimeContourTransportTomographicError_norm_tendsto_zero_ownerContourTailEstimate
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
      (fun N : ℕ => ‖finitePrimeContourTransportTomographicError N f‖)
      atTop
      (𝓝 0) := by
  have hmajorant :
      Tendsto
        (fun N : ℕ =>
          finitePrimeContourTransportTomographicErrorRemainderMajorant N f)
        atTop
        (𝓝 0) :=
    finitePrimeContourTransportTomographicErrorRemainderMajorant_tendsto_zero
      S hheight f hPhi hHorizontal
  have hfun :
      (fun N : ℕ => ‖finitePrimeContourTransportTomographicError N f‖) =
        (fun N : ℕ =>
          finitePrimeContourTransportTomographicErrorRemainderMajorant N f) := by
    funext N
    exact finitePrimeContourTransportTomographicError_norm_eq_remainderMajorant
      N f
  exact Eq.subst
    (motive := fun u : ℕ → ℝ => Tendsto u atTop (𝓝 0))
    hfun.symm
    hmajorant

/-- The finite tomographic residual tends to zero.

This is a wrapper over the norm-remainder tail estimate. -/
theorem finitePrimeContourTransportTomographicError_tendsto_zero_ownerContourTailEstimate
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
      (fun N : ℕ => finitePrimeContourTransportTomographicError N f)
      atTop
      (𝓝 0) := by
  have hnorm :
      Tendsto
        (fun N : ℕ => ‖finitePrimeContourTransportTomographicError N f‖)
        atTop
        (𝓝 0) :=
    finitePrimeContourTransportTomographicError_norm_tendsto_zero_ownerContourTailEstimate
      S
      hheight
      f
      hPhi
      hHorizontal
  have hbound :
      ∀ᶠ N in atTop,
        ‖finitePrimeContourTransportTomographicError N f‖ ≤
          ‖finitePrimeContourTransportTomographicError N f‖ :=
    Eventually.of_forall (fun _N : ℕ => le_rfl)
  exact squeeze_zero_norm' hbound hnorm

/-- The boxed finite-window coordinate-shadow remainder tends to zero.

This is the boxed-remainder wrapper over the finite tomographic residual estimate. -/
theorem finitePrimeHorizontalResidueCoordinateShadowBoxRemainder_tendsto_zero
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
      (fun N : ℕ => finitePrimeHorizontalResidueCoordinateShadowBoxRemainder N f)
      atTop
      (𝓝 0) := by
  have herror :
      Tendsto
        (fun N : ℕ => finitePrimeContourTransportTomographicError N f)
        atTop
        (𝓝 0) :=
    finitePrimeContourTransportTomographicError_tendsto_zero_ownerContourTailEstimate
      S
      hheight
      f
      hPhi
      hHorizontal
  have hfun :
      (fun N : ℕ => finitePrimeHorizontalResidueCoordinateShadowBoxRemainder N f) =
        (fun N : ℕ => finitePrimeContourTransportTomographicError N f) := by
    funext N
    exact finitePrimeHorizontalResidueCoordinateShadowBoxRemainder_eq_tomographicError
      N f
  exact Eq.subst
    (motive := fun u : ℕ → ℝ => Tendsto u atTop (𝓝 0))
    hfun.symm
    herror

/-- Finite-window box-remainder estimate for the omitted prime coordinate tail.

This is only the unfolded expression form of
`finitePrimeHorizontalResidueCoordinateShadowBoxRemainder_tendsto_zero`. -/
theorem finitePrimeHorizontalResidueCoordinateShadow_boxRemainder_tendsto_zero
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
        (∑ ι in ZetaPrimePowerIndex.box N,
          finitePrimeHorizontalResidueCoordinateShadow ι f) -
          finitePrimeHorizontalResidueShadow N f)
      atTop
      (𝓝 0) := by
  have hbox :
      Tendsto
        (fun N : ℕ => finitePrimeHorizontalResidueCoordinateShadowBoxRemainder N f)
        atTop
        (𝓝 0) :=
    finitePrimeHorizontalResidueCoordinateShadowBoxRemainder_tendsto_zero
      S hheight f hPhi hHorizontal
  have hfun :
      (fun N : ℕ =>
        (∑ ι in ZetaPrimePowerIndex.box N,
          finitePrimeHorizontalResidueCoordinateShadow ι f) -
          finitePrimeHorizontalResidueShadow N f) =
        (fun N : ℕ => finitePrimeHorizontalResidueCoordinateShadowBoxRemainder N f) := by
    funext N
    exact (finitePrimeHorizontalResidueCoordinateShadowBoxRemainder_eq N f).symm
  exact Eq.subst
    (motive := fun u : ℕ → ℝ => Tendsto u atTop (𝓝 0))
    hfun.symm
    hbox

/-- Finite-window remainder estimate for the omitted prime coordinate tail.

This is the genuine tail estimate: after finite-window contour transport, the omitted
coordinate-remainder tail is a residual finite-window error tending to zero.  The visible
tail-localization theorem below is only a named wrapper over this estimate. -/
theorem completedPrimeContourTransportCoordinateRemainderTail_remainderEstimate_tendsto_zero
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
      (fun N : ℕ => completedPrimeContourTransportCoordinateRemainderTail N f)
      atTop
      (𝓝 0) := by
  have hbox :
      Tendsto
        (fun N : ℕ => finitePrimeHorizontalResidueCoordinateShadowBoxRemainder N f)
        atTop
        (𝓝 0) :=
    finitePrimeHorizontalResidueCoordinateShadowBoxRemainder_tendsto_zero
      S hheight f hPhi hHorizontal
  have hfun :
      (fun N : ℕ => completedPrimeContourTransportCoordinateRemainderTail N f) =
        (fun N : ℕ => finitePrimeHorizontalResidueCoordinateShadowBoxRemainder N f) := by
    funext N
    exact
      completedPrimeContourTransportCoordinateRemainderTail_eq_boxRemainder
        N f
  exact Eq.subst
    (motive := fun u : ℕ → ℝ => Tendsto u atTop (𝓝 0))
    hfun.symm
    hbox

/-- The omitted prime coordinate-remainder tail vanishes after finite-window transport.

This is the tail-localization input in invariant tail-object form.  The coordinate
window-minus-shadow statement below is only this theorem transported through the definition
of `completedPrimeContourTransportCoordinateRemainderTail`. -/
theorem completedPrimeContourTransportCoordinateRemainderTail_tendsto_zero_ownerContourTailLocalization
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
      (fun N : ℕ => completedPrimeContourTransportCoordinateRemainderTail N f)
      atTop
      (𝓝 0) := by
  exact
    completedPrimeContourTransportCoordinateRemainderTail_remainderEstimate_tendsto_zero
      S
      hheight
      f
      hPhi
      hHorizontal

/-- The prime coordinate-remainder tail vanishes after finite-window renormalization.

This is the exact window-tail localization input:
`finitePrimeHorizontalResidueCoordinateShadow_window_sub_residueShadow_tendsto_zero`
shows that the finite coordinate-shadow window and the horizontal residue shadow differ by
a term tending to zero. -/
theorem finitePrimeHorizontalResidueCoordinateShadow_window_sub_residueShadow_tendsto_zero
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
        (∑ ι in ZetaPrimePowerIndex.window N,
          finitePrimeHorizontalResidueCoordinateShadow ι f) -
          finitePrimeHorizontalResidueShadow N f)
      atTop
      (𝓝 0) := by
  have htail :
      Tendsto
        (fun N : ℕ => completedPrimeContourTransportCoordinateRemainderTail N f)
        atTop
        (𝓝 0) :=
    completedPrimeContourTransportCoordinateRemainderTail_tendsto_zero_ownerContourTailLocalization
      S
      hheight
      f
      hPhi
      hHorizontal
  have hfun :
      (fun N : ℕ =>
        (∑ ι in ZetaPrimePowerIndex.window N,
          finitePrimeHorizontalResidueCoordinateShadow ι f) -
          finitePrimeHorizontalResidueShadow N f) =
        (fun N : ℕ => completedPrimeContourTransportCoordinateRemainderTail N f) := by
    funext N
    rfl
  exact Eq.subst
    (motive := fun u : ℕ → ℝ => Tendsto u atTop (𝓝 0))
    hfun.symm
    htail

/-- The prime coordinate-remainder tail vanishes after finite-window renormalization. -/
theorem completedPrimeContourTransportCoordinateRemainderTail_tendsto_zero
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
      (fun N : ℕ => completedPrimeContourTransportCoordinateRemainderTail N f)
      atTop
      (𝓝 0) := by
  exact
    completedPrimeContourTransportCoordinateRemainderTail_tendsto_zero_ownerContourTailLocalization
      S
      hheight
      f
      hPhi
      hHorizontal

/-- Completed prime contour normalization-to-heart transport.

The scheduled finite-window contour normalization lands in the two-face/GNS ordered-heart
scalar, and the omitted prime tail vanishes in the same reconstructed channel. -/
theorem completedPrimeContourNormalizationToHeart_transport
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
    completedPrimeContourRealizedFiniteWindowPairing f =
        completedPrimeContourGNSHeartScalar f ∧
      Tendsto
        (fun N : ℕ => completedPrimeContourTransportCoordinateRemainderTail N f)
        atTop
        (𝓝 0) := by
  exact
    ⟨completedPrimeContourRealizedFiniteWindowPairing_eq_GNSHeartScalar S f,
      completedPrimeContourTransportCoordinateRemainderTail_tendsto_zero
        S hheight f hPhi hHorizontal⟩

/-- Prime tail convergence after finite-window contour normalization.

This is the renormalization/tail link in the normalization-to-heart chain. -/
theorem completedPrimeContourPrimeTailRenormalization_tendsto_zero
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
      (fun N : ℕ => completedPrimeContourTransportCoordinateRemainderTail N f)
      atTop
      (𝓝 0) := by
  exact
    completedPrimeContourTransportCoordinateRemainderTail_tendsto_zero
      S hheight f hPhi hHorizontal

/-- Completed finite-window contour normalization lands in the GNS/ordered-heart scalar.

This is the scalar comparison link in the normalization-to-heart chain: after the finite
defect-square expansion, lower-weight diagonal-debt absorption, and prime tail
renormalization, the completed contour measurement is the two-face/GNS heart scalar. -/
theorem completedPrimeFiniteWindowContourNormalization_eq_GNSHeartScalar
    (S : CompletedPrimeContourTransportScheduledFamily)
    (f : ZetaAdmissibleFunction) :
    completedPrimeContourRealizedFiniteWindowPairing f =
      completedPrimeContourGNSHeartScalar f := by
  exact completedPrimeContourRealizedFiniteWindowPairing_eq_GNSHeartScalar S f

/-- Completed finite-window/GNS contour reconstruction at the ordered-heart scalar.

This is the remaining construction theorem after the finite defect-square expansion,
raw spectral/two-face extraction, and diagonal-debt absorption have been exposed as named
constituents.  It says that the completed finite-window contour measurement reconstructs
the GNS/ordered-heart scalar, and that the omitted prime tail vanishes after the
finite-window transport. -/
theorem completedPrimeFiniteWindowGNSContourReconstruction_twoFaceComparison_and_tailConvergence
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
    completedPrimeContourRealizedFiniteWindowPairing f =
        completedPrimeContourGNSHeartScalar f ∧
      Tendsto
        (fun N : ℕ => completedPrimeContourTransportCoordinateRemainderTail N f)
        atTop
        (𝓝 0) := by
  exact
    ⟨completedPrimeFiniteWindowContourNormalization_eq_GNSHeartScalar S f,
      completedPrimeContourPrimeTailRenormalization_tendsto_zero
        S hheight f hPhi hHorizontal⟩

/-- Completed prime finite-window/GNS contour realization at the two-face coefficient.

This is the construction-level GNS comparison: the completed finite-window contour scalar
is the real two-face/GNS coefficient, and the omitted prime tail vanishes after
finite-window transport. -/
theorem completedPrimeFiniteWindowGNSContourRealization_gnsCoordinateComparison_and_primeTail
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
    completedPrimeContourRealizedFiniteWindowPairing f =
        completedPrimeContourGNSHeartScalar f ∧
      Tendsto
        (fun N : ℕ => completedPrimeContourTransportCoordinateRemainderTail N f)
        atTop
        (𝓝 0) := by
  exact
    completedPrimeFiniteWindowGNSContourReconstruction_twoFaceComparison_and_tailConvergence
      S
      hheight
      f
      hPhi
      hHorizontal

/-- Completed prime finite-window/GNS coordinate comparison with the two-face coefficient. -/
theorem completedPrimeFiniteWindowGNSContourRealization_gnsCoordinateComparison
    (S : CompletedPrimeContourTransportScheduledFamily)
    (f : ZetaAdmissibleFunction) :
    completedPrimeContourRealizedFiniteWindowPairing f =
      completedPrimeContourGNSHeartScalar f := by
  exact completedPrimeFiniteWindowContourNormalization_eq_GNSHeartScalar S f

/-- The omitted prime tail vanishes after finite-window/GNS contour transport. -/
theorem completedPrimeFiniteWindowGNSContourRealization_primeTail_tendsto_after_finiteWindowTransport
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
      (fun N : ℕ => completedPrimeContourTransportCoordinateRemainderTail N f)
      atTop
      (𝓝 0) := by
  exact
    completedPrimeContourTransportCoordinateRemainderTail_tendsto_zero
      S hheight f hPhi hHorizontal

/-- Completed prime finite-window/GNS contour realization, in construction form.

The completed finite-window/GNS contour scalar realizes the raw spectral contour scalar,
and the omitted coordinate-remainder tails vanish in the same completed realization.  This
is the single construction theorem for the prime finite-window/GNS-to-raw-contour bridge. -/
theorem completedPrimeFiniteWindowGNSContourRealization_identifies_rawSpectral_and_tail_tendsto
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
    completedPrimeContourRealizedFiniteWindowPairing f =
        completedPrimeContourRealizedTimeDistributionPairing
          (convolutionAutocorrelation f) ∧
      Tendsto
        (fun N : ℕ => completedPrimeContourTransportCoordinateRemainderTail N f)
        atTop
        (𝓝 0) := by
  have hgns :
    completedPrimeContourRealizedFiniteWindowPairing f =
        completedPrimeContourGNSHeartScalar f :=
    completedPrimeFiniteWindowGNSContourRealization_gnsCoordinateComparison S f
  have hraw :
      completedPrimeContourRealizedTimeDistributionPairing
          (convolutionAutocorrelation f) =
        completedPrimeContourGNSHeartScalar f :=
    completedPrimeContourRawSpectralPairing_eq_twoFaceGNSBoundaryCoefficient_re f
  have htail :
      Tendsto
        (fun N : ℕ => completedPrimeContourTransportCoordinateRemainderTail N f)
        atTop
        (𝓝 0) :=
    completedPrimeFiniteWindowGNSContourRealization_primeTail_tendsto_after_finiteWindowTransport
      S
      hheight
      f
      hPhi
      hHorizontal
  exact ⟨hgns.trans hraw.symm, htail⟩

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
