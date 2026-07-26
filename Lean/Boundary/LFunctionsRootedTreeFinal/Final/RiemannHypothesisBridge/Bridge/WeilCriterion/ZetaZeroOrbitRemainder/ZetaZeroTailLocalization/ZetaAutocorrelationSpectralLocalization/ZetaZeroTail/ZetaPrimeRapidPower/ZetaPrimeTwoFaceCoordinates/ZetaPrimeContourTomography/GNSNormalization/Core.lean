import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaZeroTail.ZetaPrimeRapidPower.ZetaPrimeTwoFaceCoordinates.ZetaPrimeContourTomography.TailEstimates.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaCompletedHilbertSource.ZetaHermitianPacket.HermitianBoundaryDefect

/-!
# Prime contour GNS core

This file owns the scalar GNS definitions and scalar comparison lemmas shared by
the schedule-parametric and concrete tail-normalization layers.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open Filter
open scoped Topology

namespace ZetaAdmissibleFunction

/-- The completed finite-window contour scalar for the autocorrelation prime channel. -/
noncomputable def completedPrimeContourRealizedFiniteWindowPairing
    (f : ZetaAdmissibleFunction) : ℝ :=
  completedPrimeTimeDistributionPairing (convolutionAutocorrelation f)

/-- The ordered-heart scalar reconstructed by the completed prime two-face/GNS channel. -/
noncomputable def completedPrimeContourGNSHeartScalar
    (f : ZetaAdmissibleFunction) : ℝ :=
  Complex.re (zetaCompletedPrimeTwoFaceGNSBoundaryCoefficient f)

/-- Finite completed prime defect-square expansion in the contour-realization vocabulary. -/
theorem finitePrimeContourGNS_defectSquareExpansion
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    zetaCompletedPrimeDefectKernelPositiveWindow N f +
        zetaCompletedPrimeTwoFaceGNSMatrixCoefficientWindow N f =
      zetaCompletedPrimeDefectKernelDiagonalDebtWindow N f := by
  exact zetaCompletedPrimeDefectKernelPositiveWindow_add_twoFaceWindow_eq_diagonalDebtWindow
    N f

/-- Completed diagonal-debt absorption for the prime two-face/GNS boundary coefficient. -/
theorem completedPrimeContourGNS_diagonalDebtAbsorption
    (f : ZetaAdmissibleFunction) :
      zetaCompletedPrimeDefectKernelPositiveForm f =
      zetaCompletedPrimeDefectKernelDiagonalDebt f +
        zetaCompletedPrimeTwoFaceGNSBoundaryCoefficient f := by
  exact zetaCompletedPrimeDefectKernelPositiveForm_eq_diagonalDebt_add_boundaryCoefficient
    f

/-- The raw spectral contour scalar is the real part of the completed two-face/GNS boundary
coefficient. -/
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

/-- Finite-window expansion and diagonal-debt absorption reach the GNS heart scalar. -/
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
finite-window contour scalar with the raw spectral contour scalar. -/
theorem completedPrimeContourFiniteWindowExpansion_diagonalDebtAbsorption_eq_rawSpectralPairing
    (S : CompletedPrimeContourTransportScheduledFamily)
    (f : ZetaAdmissibleFunction) :
    completedPrimeContourRealizedFiniteWindowPairing f =
      completedPrimeContourRealizedTimeDistributionPairing
        (convolutionAutocorrelation f) := by
  exact completedPrimeContourRealizedFiniteWindowPairing_eq_rawSpectralPairing S f

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
