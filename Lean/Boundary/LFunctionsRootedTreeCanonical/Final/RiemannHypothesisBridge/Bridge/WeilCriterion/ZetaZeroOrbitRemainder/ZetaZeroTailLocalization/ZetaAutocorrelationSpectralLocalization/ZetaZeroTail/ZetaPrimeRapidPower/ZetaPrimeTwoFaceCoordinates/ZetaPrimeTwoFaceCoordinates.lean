import Boundary.LFunctions.ZetaCompletedPositiveBoundary
import Boundary.LFunctions.ZetaPrimeContourTomography
import Boundary.LFunctions.ZetaExplicitFormulaComplexAnalysis

/-!
# Prime two-face coordinates

This file owns the completed prime two-face coordinates and the finite time/contour
prime-window convergence statements used by horizontal decay and final tomography.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open Filter
open scoped Topology

namespace ZetaAdmissibleFunction

/-- The real completed two-face/GNS coordinate attached to one prime-power index. -/
noncomputable def completedPrimeTwoFaceGNSRealCoordinate
    (ι : ZetaPrimePowerIndex) (f : ZetaAdmissibleFunction) : ℝ :=
  Complex.re
    (zetaCompletedPrimeSpectralAmplitudeIndex ι f *
        star (zetaCompletedPrimeOppositeSpectralAmplitudeIndex ι f) +
      star
        (zetaCompletedPrimeSpectralAmplitudeIndex ι f *
          star (zetaCompletedPrimeOppositeSpectralAmplitudeIndex ι f)))

/-- The real completed two-face boundary coordinate attached to one prime-power index.

This is the real shadow of the completed two-face/GNS boundary coordinate.  It is not the
raw real-lag off-diagonal coordinate; the raw time-side channel reaches this coordinate only
after completed prime tomography/transport. -/
noncomputable def completedPrimeTwoFaceGNSBoundaryRealCoordinate
    (ι : ZetaPrimePowerIndex) (f : ZetaAdmissibleFunction) : ℝ :=
  Complex.re (-zetaCompletedPrimeTwoFaceGNSSymmetrizedCoordinate ι f)

/-- The completed two-face boundary real coordinate is the real part of the signed
symmetrized two-face/GNS packet coordinate. -/
theorem completedPrimeTwoFaceGNSBoundaryRealCoordinate_eq_neg_symmetrizedCoordinate_re
    (ι : ZetaPrimePowerIndex) (f : ZetaAdmissibleFunction) :
    completedPrimeTwoFaceGNSBoundaryRealCoordinate ι f =
      Complex.re (-zetaCompletedPrimeTwoFaceGNSSymmetrizedCoordinate ι f) := by
  rfl

/-- The completed two-face boundary real-coordinate sum reconstructs the completed
two-face boundary coefficient.

This is the owner holographic reconstruction theorem for the completed prime two-face
coordinate layer: the completed real boundary-coordinate sum and the completed
two-face boundary coefficient are the same reconstructed prime boundary scalar. -/
theorem completedPrimeTwoFaceBoundaryRealCoordinate_tsum_eq_coefficient_re_ownerCoordinates
    (f : ZetaAdmissibleFunction) :
    (∑' ι : ZetaPrimePowerIndex,
        completedPrimeTwoFaceGNSBoundaryRealCoordinate ι f) =
      Complex.re (zetaCompletedPrimeTwoFaceGNSBoundaryCoefficient f) := by
  have hcoordinate :
      (∑' ι : ZetaPrimePowerIndex,
          completedPrimeTwoFaceGNSBoundaryRealCoordinate ι f) =
        ∑' ι : ZetaPrimePowerIndex,
          Complex.re (-zetaCompletedPrimeTwoFaceGNSSymmetrizedCoordinate ι f) := by
    exact tsum_congr
      (fun ι : ZetaPrimePowerIndex =>
        completedPrimeTwoFaceGNSBoundaryRealCoordinate_eq_neg_symmetrizedCoordinate_re
          ι f)
  have hre :
      (∑' ι : ZetaPrimePowerIndex,
          Complex.re (-zetaCompletedPrimeTwoFaceGNSSymmetrizedCoordinate ι f)) =
        Complex.re
          (∑' ι : ZetaPrimePowerIndex,
            -zetaCompletedPrimeTwoFaceGNSSymmetrizedCoordinate ι f) := by
    exact
      (Complex.tsum_re
        (fun ι : ZetaPrimePowerIndex =>
          -zetaCompletedPrimeTwoFaceGNSSymmetrizedCoordinate ι f)).symm
  have hboundary :
      (∑' ι : ZetaPrimePowerIndex,
          -zetaCompletedPrimeTwoFaceGNSSymmetrizedCoordinate ι f) =
        zetaCompletedPrimeTwoFaceGNSBoundaryCoefficient f :=
    zetaCompletedPrimeTwoFaceGNSBoundaryCoordinate_tsum_eq_boundaryCoefficient f
  exact hcoordinate.trans (hre.trans (congrArg Complex.re hboundary))

/-- The finite time-side prime windows converge to the completed time-side prime
distribution. -/
theorem finitePrimeTimeDistributionWindow_tendsto_completed
    (f : ZetaAdmissibleFunction) :
    Tendsto
      (fun N : ℕ =>
        finitePrimeTimeDistributionWindow N (convolutionAutocorrelation f))
      atTop
      (𝓝 (completedPrimeTimeDistributionPairing (convolutionAutocorrelation f))) := by
  have hcoordinate :
      ∀ ι : ZetaPrimePowerIndex,
        zetaPrimeOffDiagonalCoordinate ι f =
          completedPrimeTimeDistributionCoordinate ι
            (convolutionAutocorrelation f) := by
    intro ι
    exact
      (completedPrimeTimeDistributionCoordinate_convolutionAutocorrelation_eq_physical
        ι f).symm
  have htime :
      Summable (fun ι : ZetaPrimePowerIndex =>
        completedPrimeTimeDistributionCoordinate ι
          (convolutionAutocorrelation f)) :=
    (summable_zetaPrimeOffDiagonalCoordinate f).congr hcoordinate
  unfold finitePrimeTimeDistributionWindow
  exact ZetaPrimePowerIndex.tendsto_sum_window_tsum_of_summable
    (fun ι : ZetaPrimePowerIndex =>
      completedPrimeTimeDistributionCoordinate ι (convolutionAutocorrelation f))
    htime
    (fun ι hι => by
      have hphysical :
          completedPrimeTimeDistributionCoordinate ι (convolutionAutocorrelation f) =
            zetaPrimeOffDiagonalCoordinate ι f :=
        completedPrimeTimeDistributionCoordinate_convolutionAutocorrelation_eq_physical ι f
      exact hphysical.trans
        (zetaPrimeOffDiagonalCoordinate_eq_zero_of_not_isGenuine ι f hι))

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
