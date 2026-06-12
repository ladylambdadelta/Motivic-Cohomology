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

This is the time-side prime off-diagonal coordinate.  The spectral two-face coefficient is a
separate completed reconstruction of the sum of these coordinates, not a pointwise
definition. -/
noncomputable def completedPrimeTwoFaceGNSBoundaryRealCoordinate
    (ι : ZetaPrimePowerIndex) (f : ZetaAdmissibleFunction) : ℝ :=
  zetaPrimeOffDiagonalCoordinate ι f

/-- Coordinate prime tomography: the physical off-diagonal coordinate is the completed
two-face boundary coordinate.

This is the local time/spectral reconstruction theorem. -/
theorem zetaPrimeOffDiagonalCoordinate_eq_completedPrimeTwoFaceGNSBoundaryRealCoordinate
    (ι : ZetaPrimePowerIndex) (f : ZetaAdmissibleFunction) :
    zetaPrimeOffDiagonalCoordinate ι f =
      completedPrimeTwoFaceGNSBoundaryRealCoordinate ι f := by
  rfl

/-- Prime tomography at one prime-power coordinate: the time-side autocorrelation coordinate
reconstructs the completed two-face/GNS boundary coordinate.

This is the coordinate form of the completed contour/log-coordinate reconstruction theorem.
It is intentionally stated before the completed summation theorem so the global prime
realization cannot hide coordinate-level content. -/
theorem completedPrimeTimeDistributionCoordinate_convolutionAutocorrelation_eq_twoFaceGNSRealCoordinate
    (ι : ZetaPrimePowerIndex) (f : ZetaAdmissibleFunction) :
    completedPrimeTimeDistributionCoordinate ι (convolutionAutocorrelation f) =
      completedPrimeTwoFaceGNSBoundaryRealCoordinate ι f := by
  have hphysical :
      completedPrimeTimeDistributionCoordinate ι (convolutionAutocorrelation f) =
        zetaPrimeOffDiagonalCoordinate ι f :=
    completedPrimeTimeDistributionCoordinate_convolutionAutocorrelation_eq_physical
      ι f
  have htomography :
      zetaPrimeOffDiagonalCoordinate ι f =
        completedPrimeTwoFaceGNSBoundaryRealCoordinate ι f :=
    zetaPrimeOffDiagonalCoordinate_eq_completedPrimeTwoFaceGNSBoundaryRealCoordinate
      ι f
  exact hphysical.trans htomography

/-- The completed two-face boundary real coordinates are summable over prime powers. -/
theorem summable_completedPrimeTwoFaceGNSBoundaryRealCoordinate
    (f : ZetaAdmissibleFunction) :
    Summable (fun ι : ZetaPrimePowerIndex =>
      completedPrimeTwoFaceGNSBoundaryRealCoordinate ι f) := by
  exact summable_zetaPrimeOffDiagonalCoordinate f

/-- The finite time-side prime windows converge to the completed time-side prime
distribution. -/
theorem finitePrimeTimeDistributionWindow_tendsto_completed
    (f : ZetaAdmissibleFunction) :
    Tendsto
      (fun N : ℕ =>
        finitePrimeTimeDistributionWindow N (convolutionAutocorrelation f))
      atTop
      (𝓝 (completedPrimeTimeDistributionPairing (convolutionAutocorrelation f))) := by
  have hboundary :
      Summable (fun ι : ZetaPrimePowerIndex =>
        completedPrimeTwoFaceGNSBoundaryRealCoordinate ι f) :=
    summable_completedPrimeTwoFaceGNSBoundaryRealCoordinate f
  have hcoordinate :
      ∀ ι : ZetaPrimePowerIndex,
        completedPrimeTwoFaceGNSBoundaryRealCoordinate ι f =
          completedPrimeTimeDistributionCoordinate ι
            (convolutionAutocorrelation f) := by
    intro ι
    exact
      (completedPrimeTimeDistributionCoordinate_convolutionAutocorrelation_eq_twoFaceGNSRealCoordinate
        ι f).symm
  have htime :
      Summable (fun ι : ZetaPrimePowerIndex =>
        completedPrimeTimeDistributionCoordinate ι
          (convolutionAutocorrelation f)) :=
    hboundary.congr hcoordinate
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
