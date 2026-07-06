import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaZeroTail.ZetaPrimeRapidPower.ZetaPrimeTwoFaceCoordinates.ZetaPrimeContourTomography.TailEstimates.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaCompletedHilbertSource.ZetaHermitianPacket.HermitianBoundaryDefect

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

/-- The completed finite-window contour scalar for the autocorrelation prime channel.

The scalar is owned as the limit of finite contour windows through the completed
finite-window/GNS realization.  It is separated from the raw spectral scalar
`completedPrimeContourRealizedTimeDistributionPairing`; the comparison between the two is
part of the completed finite-window/GNS contour realization theorem below. -/
noncomputable def completedPrimeContourRealizedFiniteWindowPairing
    (f : ZetaAdmissibleFunction) : ℝ :=
  completedPrimeTimeDistributionPairing (convolutionAutocorrelation f)

/-- The ordered-heart scalar reconstructed by the completed prime two-face/GNS channel.

This is the scalar target of prime contour tomography.  The raw contour presentation is
compared to this scalar only after finite-window/GNS reconstruction. -/
noncomputable def completedPrimeContourGNSHeartScalar
    (f : ZetaAdmissibleFunction) : ℝ :=
  Complex.re (zetaCompletedPrimeTwoFaceGNSBoundaryCoefficient f)

/-- Finite completed prime defect-square expansion in the contour-realization vocabulary.

This is the finite GNS/defect-kernel identity: the positive defect square plus the
two-face cross term is the finite diagonal debt. -/
theorem finitePrimeContourGNS_defectSquareExpansion
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    zetaCompletedPrimeDefectKernelPositiveWindow N f +
        zetaCompletedPrimeTwoFaceGNSMatrixCoefficientWindow N f =
      zetaCompletedPrimeDefectKernelDiagonalDebtWindow N f := by
  exact zetaCompletedPrimeDefectKernelPositiveWindow_add_twoFaceWindow_eq_diagonalDebtWindow
    N f

/-- Completed diagonal-debt absorption for the prime two-face/GNS boundary coefficient.

The positive defect kernel absorbs the diagonal debt and leaves the signed two-face boundary
coefficient.  This is the completed form of the finite defect-square expansion. -/
theorem completedPrimeContourGNS_diagonalDebtAbsorption
    (f : ZetaAdmissibleFunction) :
      zetaCompletedPrimeDefectKernelPositiveForm f =
      zetaCompletedPrimeDefectKernelDiagonalDebt f +
        zetaCompletedPrimeTwoFaceGNSBoundaryCoefficient f := by
  exact zetaCompletedPrimeDefectKernelPositiveForm_eq_diagonalDebt_add_boundaryCoefficient
    f

/-- The raw spectral contour scalar is the real part of the completed two-face/GNS boundary
coefficient.

This is the raw spectral/two-face identification in the contour-realization owner file. -/
theorem completedPrimeContourRawSpectralPairing_eq_twoFaceGNSBoundaryCoefficient_re
    (f : ZetaAdmissibleFunction) :
    completedPrimeContourRealizedTimeDistributionPairing
        (convolutionAutocorrelation f) =
      completedPrimeContourGNSHeartScalar f := by
  have hspectral :
      completedPrimeContourRealizedTimeDistributionPairing
          (convolutionAutocorrelation f) =
        completedPrimeSpectralDistributionPairing
          (zetaCompletedSpectralLaplaceTransform (convolutionAutocorrelation f)) :=
    completedPrimeContourRealizedTimeDistribution_eq_spectralPrimePowerContribution
      (convolutionAutocorrelation f)
  have hchannel :
      completedSpectralPrimeOffDiagonalChannel f =
        completedPrimeSpectralDistributionPairing
          (zetaCompletedSpectralLaplaceTransform (convolutionAutocorrelation f)) :=
    completedSpectralPrimeOffDiagonalChannel_eq_spectralDistributionPairing f
  have htwoFace :
      completedSpectralPrimeOffDiagonalChannel f =
        completedPrimeContourGNSHeartScalar f := by
    exact
      completedSpectralPrimeOffDiagonalChannel_eq_completedTwoFaceBoundaryCoefficient_re
        f
  exact hspectral.trans (hchannel.symm.trans htwoFace)

/-- Finite-window expansion and diagonal-debt absorption reach the GNS heart scalar.

This is the finite-window defect-square expansion and diagonal-debt absorption bridge:
it identifies the completed finite-window contour measurement with the two-face/GNS
ordered-heart scalar before the separate raw spectral/two-face comparison is applied. -/
theorem completedPrimeContourFiniteWindowExpansion_diagonalDebtAbsorption_eq_GNSHeartScalar
    (S : CompletedPrimeContourTransportScheduledFamily)
    (f : ZetaAdmissibleFunction) :
    completedPrimeContourRealizedFiniteWindowPairing f =
      completedPrimeContourGNSHeartScalar f := by
  have htime :
      completedPrimeContourRealizedFiniteWindowPairing f =
        completedPrimeTimeDistributionPairing (convolutionAutocorrelation f) := by
    rfl
  have hphysical :
      completedPrimeTimeDistributionPairing (convolutionAutocorrelation f) =
        completedPrimeOffDiagonalChannel f :=
    completedPrimeTimeDistributionPairing_eq_completedPrimeOffDiagonalChannel f
  have hgns :
      completedPrimeOffDiagonalChannel f =
        completedPrimeContourGNSHeartScalar f := by
    exact
      completedPrimeOffDiagonalChannel_eq_completedTwoFaceGNSBoundaryCoefficient_re_ownerDistributionTransport
        f
        (completedFiniteWindowPrimeDistributionReconstruction_of_scheduledContourFamily
          S f)
  exact htime.trans (hphysical.trans hgns)

/-- Finite-window contour normalization lands in the GNS/ordered-heart scalar. -/
theorem completedPrimeContourRealizedFiniteWindowPairing_eq_GNSHeartScalar
    (S : CompletedPrimeContourTransportScheduledFamily)
    (f : ZetaAdmissibleFunction) :
    completedPrimeContourRealizedFiniteWindowPairing f =
      completedPrimeContourGNSHeartScalar f := by
  exact
    completedPrimeContourFiniteWindowExpansion_diagonalDebtAbsorption_eq_GNSHeartScalar
      S
      f

/-- Finite-window contour normalization agrees with the raw spectral contour scalar. -/
theorem completedPrimeContourRealizedFiniteWindowPairing_eq_rawSpectralPairing
    (S : CompletedPrimeContourTransportScheduledFamily)
    (f : ZetaAdmissibleFunction) :
    completedPrimeContourRealizedFiniteWindowPairing f =
      completedPrimeContourRealizedTimeDistributionPairing
        (convolutionAutocorrelation f) := by
  exact
    (completedPrimeContourRealizedFiniteWindowPairing_eq_GNSHeartScalar S f).trans
      (completedPrimeContourRawSpectralPairing_eq_twoFaceGNSBoundaryCoefficient_re f).symm

/-- Finite-window expansion and diagonal-debt absorption identify the completed
finite-window contour scalar with the raw spectral contour scalar.

This is the local contour theorem requested by the finite-window/GNS bridge: first the
finite-window scalar is reconstructed as the GNS heart scalar, then the raw spectral
two-face comparison identifies that heart scalar with the raw contour presentation. -/
theorem completedPrimeContourFiniteWindowExpansion_diagonalDebtAbsorption_eq_rawSpectralPairing
    (S : CompletedPrimeContourTransportScheduledFamily)
    (f : ZetaAdmissibleFunction) :
    completedPrimeContourRealizedFiniteWindowPairing f =
      completedPrimeContourRealizedTimeDistributionPairing
        (convolutionAutocorrelation f) := by
  exact completedPrimeContourRealizedFiniteWindowPairing_eq_rawSpectralPairing S f

/-- The explicit finite-window tail majorant tends to zero.

This is the remaining analytic tail-remainder estimate after support reduction and
finite-window remainder naming. -/
theorem finitePrimeContourTransportTomographicErrorRemainderMajorant_tendsto_zero_core
    (S : CompletedPrimeContourTransportScheduledFamily)
    (f : ZetaAdmissibleFunction)
    (hPhi : ZetaPhiAnalyticControl (convolutionAutocorrelation f))
    (hLog : CompletedZetaNegLogDerivControl (convolutionAutocorrelation f)) :
    Tendsto
      (fun N : ℕ =>
        finitePrimeContourTransportTomographicErrorRemainderMajorant N f)
      atTop
      (𝓝 0) := by
  have hbox :
      Tendsto
        (fun N : ℕ => ‖finitePrimeHorizontalResidueCoordinateShadowBoxRemainder N f‖)
        atTop
        (𝓝 0) :=
    finitePrimeHorizontalResidueCoordinateShadowBoxRemainder_norm_tendsto_zero_ownerTailEstimate
      S
      f
      hPhi
      hLog
  have hfun :
      (fun N : ℕ =>
          finitePrimeContourTransportTomographicErrorRemainderMajorant N f) =
        (fun N : ℕ => ‖finitePrimeHorizontalResidueCoordinateShadowBoxRemainder N f‖) := by
    funext N
    have hmajorant :
        finitePrimeContourTransportTomographicErrorRemainderMajorant N f =
          ‖finitePrimeContourTransportTomographicError N f‖ :=
      (finitePrimeContourTransportTomographicError_norm_eq_remainderMajorant N f).symm
    have hbox :
        ‖finitePrimeContourTransportTomographicError N f‖ =
          ‖finitePrimeHorizontalResidueCoordinateShadowBoxRemainder N f‖ := by
      exact congrArg norm
        (finitePrimeHorizontalResidueCoordinateShadowBoxRemainder_eq_tomographicError
          N f).symm
    exact hmajorant.trans hbox
  exact Eq.subst
    (motive := fun u : ℕ → ℝ => Tendsto u atTop (𝓝 0))
    hfun.symm
    hbox

/-- The explicit finite-window tail majorant tends to zero.

This is the remaining analytic tail-remainder estimate after support reduction and
finite-window remainder naming. -/
theorem finitePrimeContourTransportTomographicErrorRemainderMajorant_tendsto_zero
    (S : CompletedPrimeContourTransportScheduledFamily)
    (f : ZetaAdmissibleFunction)
    (hPhi : ZetaPhiAnalyticControl (convolutionAutocorrelation f))
    (hLog : CompletedZetaNegLogDerivControl (convolutionAutocorrelation f)) :
    Tendsto
      (fun N : ℕ =>
        finitePrimeContourTransportTomographicErrorRemainderMajorant N f)
      atTop
      (𝓝 0) := by
  exact
    finitePrimeContourTransportTomographicErrorRemainderMajorant_tendsto_zero_core
      S f hPhi hLog

/-- Norm convergence of the finite tomographic residual remainder.

This is the remaining analytic tail estimate after support reduction and the pointwise
remainder bound: the finite tomographic residual has norm tending to zero. -/
theorem finitePrimeContourTransportTomographicError_norm_tendsto_zero_ownerContourTailEstimate
    (S : CompletedPrimeContourTransportScheduledFamily)
    (f : ZetaAdmissibleFunction)
    (hPhi : ZetaPhiAnalyticControl (convolutionAutocorrelation f))
    (hLog : CompletedZetaNegLogDerivControl (convolutionAutocorrelation f)) :
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
      S f hPhi hLog
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
    (f : ZetaAdmissibleFunction)
    (hPhi : ZetaPhiAnalyticControl (convolutionAutocorrelation f))
    (hLog : CompletedZetaNegLogDerivControl (convolutionAutocorrelation f)) :
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
      f
      hPhi
      hLog
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
    (f : ZetaAdmissibleFunction)
    (hPhi : ZetaPhiAnalyticControl (convolutionAutocorrelation f))
    (hLog : CompletedZetaNegLogDerivControl (convolutionAutocorrelation f)) :
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
      f
      hPhi
      hLog
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
    (f : ZetaAdmissibleFunction)
    (hPhi : ZetaPhiAnalyticControl (convolutionAutocorrelation f))
    (hLog : CompletedZetaNegLogDerivControl (convolutionAutocorrelation f)) :
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
      S f hPhi hLog
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
    (f : ZetaAdmissibleFunction)
    (hPhi : ZetaPhiAnalyticControl (convolutionAutocorrelation f))
    (hLog : CompletedZetaNegLogDerivControl (convolutionAutocorrelation f)) :
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
      S f hPhi hLog
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
    (f : ZetaAdmissibleFunction)
    (hPhi : ZetaPhiAnalyticControl (convolutionAutocorrelation f))
    (hLog : CompletedZetaNegLogDerivControl (convolutionAutocorrelation f)) :
    Tendsto
      (fun N : ℕ => completedPrimeContourTransportCoordinateRemainderTail N f)
      atTop
      (𝓝 0) := by
  exact
    completedPrimeContourTransportCoordinateRemainderTail_remainderEstimate_tendsto_zero
      S
      f
      hPhi
      hLog

/-- The prime coordinate-remainder tail vanishes after finite-window renormalization.

This is the exact window-tail localization input:
`finitePrimeHorizontalResidueCoordinateShadow_window_sub_residueShadow_tendsto_zero`
shows that the finite coordinate-shadow window and the horizontal residue shadow differ by
a term tending to zero. -/
theorem finitePrimeHorizontalResidueCoordinateShadow_window_sub_residueShadow_tendsto_zero
    (S : CompletedPrimeContourTransportScheduledFamily)
    (f : ZetaAdmissibleFunction)
    (hPhi : ZetaPhiAnalyticControl (convolutionAutocorrelation f))
    (hLog : CompletedZetaNegLogDerivControl (convolutionAutocorrelation f)) :
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
      f
      hPhi
      hLog
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
    (f : ZetaAdmissibleFunction)
    (hPhi : ZetaPhiAnalyticControl (convolutionAutocorrelation f))
    (hLog : CompletedZetaNegLogDerivControl (convolutionAutocorrelation f)) :
    Tendsto
      (fun N : ℕ => completedPrimeContourTransportCoordinateRemainderTail N f)
      atTop
      (𝓝 0) := by
  exact
    completedPrimeContourTransportCoordinateRemainderTail_tendsto_zero_ownerContourTailLocalization
      S
      f
      hPhi
      hLog

/-- Completed prime contour normalization-to-heart transport.

The scheduled finite-window contour normalization lands in the two-face/GNS ordered-heart
scalar, and the omitted prime tail vanishes in the same reconstructed channel. -/
theorem completedPrimeContourNormalizationToHeart_transport
    (S : CompletedPrimeContourTransportScheduledFamily)
    (f : ZetaAdmissibleFunction)
    (hPhi : ZetaPhiAnalyticControl (convolutionAutocorrelation f))
    (hLog : CompletedZetaNegLogDerivControl (convolutionAutocorrelation f)) :
    completedPrimeContourRealizedFiniteWindowPairing f =
        completedPrimeContourGNSHeartScalar f ∧
      Tendsto
        (fun N : ℕ => completedPrimeContourTransportCoordinateRemainderTail N f)
        atTop
        (𝓝 0) := by
  exact
    ⟨completedPrimeContourRealizedFiniteWindowPairing_eq_GNSHeartScalar S f,
      completedPrimeContourTransportCoordinateRemainderTail_tendsto_zero
        S f hPhi hLog⟩

/-- Prime tail convergence after finite-window contour normalization.

This is the renormalization/tail link in the normalization-to-heart chain. -/
theorem completedPrimeContourPrimeTailRenormalization_tendsto_zero
    (S : CompletedPrimeContourTransportScheduledFamily)
    (f : ZetaAdmissibleFunction)
    (hPhi : ZetaPhiAnalyticControl (convolutionAutocorrelation f))
    (hLog : CompletedZetaNegLogDerivControl (convolutionAutocorrelation f)) :
    Tendsto
      (fun N : ℕ => completedPrimeContourTransportCoordinateRemainderTail N f)
      atTop
      (𝓝 0) := by
  exact
    completedPrimeContourTransportCoordinateRemainderTail_tendsto_zero
      S f hPhi hLog

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
    (f : ZetaAdmissibleFunction)
    (hPhi : ZetaPhiAnalyticControl (convolutionAutocorrelation f))
    (hLog : CompletedZetaNegLogDerivControl (convolutionAutocorrelation f)) :
    completedPrimeContourRealizedFiniteWindowPairing f =
        completedPrimeContourGNSHeartScalar f ∧
      Tendsto
        (fun N : ℕ => completedPrimeContourTransportCoordinateRemainderTail N f)
        atTop
        (𝓝 0) := by
  exact
    ⟨completedPrimeFiniteWindowContourNormalization_eq_GNSHeartScalar S f,
      completedPrimeContourPrimeTailRenormalization_tendsto_zero
        S f hPhi hLog⟩

/-- Completed prime finite-window/GNS contour realization at the two-face coefficient.

This is the construction-level GNS comparison: the completed finite-window contour scalar
is the real two-face/GNS coefficient, and the omitted prime tail vanishes after
finite-window transport. -/
theorem completedPrimeFiniteWindowGNSContourRealization_gnsCoordinateComparison_and_primeTail
    (S : CompletedPrimeContourTransportScheduledFamily)
    (f : ZetaAdmissibleFunction)
    (hPhi : ZetaPhiAnalyticControl (convolutionAutocorrelation f))
    (hLog : CompletedZetaNegLogDerivControl (convolutionAutocorrelation f)) :
    completedPrimeContourRealizedFiniteWindowPairing f =
        completedPrimeContourGNSHeartScalar f ∧
      Tendsto
        (fun N : ℕ => completedPrimeContourTransportCoordinateRemainderTail N f)
        atTop
        (𝓝 0) := by
  exact
    completedPrimeFiniteWindowGNSContourReconstruction_twoFaceComparison_and_tailConvergence
      S
      f
      hPhi
      hLog

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
    (f : ZetaAdmissibleFunction)
    (hPhi : ZetaPhiAnalyticControl (convolutionAutocorrelation f))
    (hLog : CompletedZetaNegLogDerivControl (convolutionAutocorrelation f)) :
    Tendsto
      (fun N : ℕ => completedPrimeContourTransportCoordinateRemainderTail N f)
      atTop
      (𝓝 0) := by
  exact
    completedPrimeContourTransportCoordinateRemainderTail_tendsto_zero
      S f hPhi hLog

/-- Completed prime finite-window/GNS contour realization, in construction form.

The completed finite-window/GNS contour scalar realizes the raw spectral contour scalar,
and the omitted coordinate-remainder tails vanish in the same completed realization.  This
is the single construction theorem for the prime finite-window/GNS-to-raw-contour bridge. -/
theorem completedPrimeFiniteWindowGNSContourRealization_identifies_rawSpectral_and_tail_tendsto
    (S : CompletedPrimeContourTransportScheduledFamily)
    (f : ZetaAdmissibleFunction)
    (hPhi : ZetaPhiAnalyticControl (convolutionAutocorrelation f))
    (hLog : CompletedZetaNegLogDerivControl (convolutionAutocorrelation f)) :
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
      f
      hPhi
      hLog
  exact ⟨hgns.trans hraw.symm, htail⟩

/-- Completed prime finite-window/GNS contour realization.

This compatibility wrapper packages the two split prime owner facts:
`completedPrimeContourFiniteWindowExpansion_diagonalDebtAbsorption_eq_GNSHeartScalar`
and `finitePrimeHorizontalResidueCoordinateShadow_window_sub_residueShadow_tendsto_zero`,
under the historical horizontal-decay owner name consumed by the finite-window transport
layer. -/
theorem completedPrimeContourFiniteWindowGNSRealization_ownerHorizontalDecay
    (S : CompletedPrimeContourTransportScheduledFamily)
    (f : ZetaAdmissibleFunction)
    (hPhi : ZetaPhiAnalyticControl (convolutionAutocorrelation f))
    (hLog : CompletedZetaNegLogDerivControl (convolutionAutocorrelation f)) :
    completedPrimeContourRealizedFiniteWindowPairing f =
        completedPrimeContourRealizedTimeDistributionPairing
          (convolutionAutocorrelation f) ∧
      Tendsto
        (fun N : ℕ => completedPrimeContourTransportCoordinateRemainderTail N f)
        atTop
        (𝓝 0) := by
  exact
    completedPrimeFiniteWindowGNSContourRealization_identifies_rawSpectral_and_tail_tendsto
      S
      f
      hPhi
      hLog


end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
