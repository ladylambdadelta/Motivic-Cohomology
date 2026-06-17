import Boundary.LFunctions.ZetaPrimeHorizontalDecay

/-!
# Prime two-face tomography

This file owns the final completed prime two-face tomography statements consumed by
positive boundary descent.  Coordinate, analytic-control, and horizontal-decay
owners live in upstream prime files.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open Filter
open scoped Topology

namespace ZetaAdmissibleFunction

/-- Generic completed-window comparison.

If two finite-window systems have completed limits and their window difference is a
remainder tending to zero, then the completed limits agree. -/
theorem completedWindowLimits_eq_of_sub_tendsto_zero
    {W C R : ℕ → ℝ} {LW LC : ℝ}
    (hW : Tendsto W atTop (𝓝 LW))
    (hC : Tendsto C atTop (𝓝 LC))
    (hsub : (fun N : ℕ => C N - W N) = R)
    (hR : Tendsto R atTop (𝓝 0)) :
    LW = LC := by
  have hdiff :
      Tendsto
        (fun N : ℕ => C N - W N)
        atTop
        (𝓝 (LC - LW)) :=
    hC.sub hW
  have hzero :
      Tendsto
        (fun N : ℕ => C N - W N)
        atTop
        (𝓝 0) :=
    Eq.subst
      (motive := fun u : ℕ → ℝ => Tendsto u atTop (𝓝 0))
      hsub.symm
      hR
  have hsubZero : LC - LW = 0 :=
    tendsto_nhds_unique hdiff hzero
  have hLCeqLW : LC = LW := by
    calc
      LC = LC - LW + LW := by
        exact (sub_add_cancel LC LW).symm
      _ = 0 + LW := by
        exact congrArg (fun x : ℝ => x + LW) hsubZero
      _ = LW := by
        exact zero_add LW
  exact hLCeqLW.symm

/-- Finite time-side prime windows converge to the completed time-side prime pairing. -/
theorem finitePrimeTimeDistributionWindow_tendsto_completedTimePairing_ownerTomography
    (f : ZetaAdmissibleFunction) :
    Tendsto
      (fun N : ℕ =>
        finitePrimeTimeDistributionWindow N (convolutionAutocorrelation f))
      atTop
      (𝓝 (completedPrimeTimeDistributionPairing (convolutionAutocorrelation f))) := by
  exact finitePrimeTimeDistributionWindow_tendsto_completed f

/-- Finite contour-realized prime windows converge to their completed finite-window
contour scalar.

This is not a coordinate summability theorem; it is the finite-window horizontal transport
limit already supplied by the horizontal-decay owner. -/
theorem finitePrimeContourRealizedTimeDistributionWindow_tendsto_completedFiniteWindowPairing_ownerTomography
    (f : ZetaAdmissibleFunction) :
    Tendsto
      (fun N : ℕ =>
        finitePrimeContourRealizedTimeDistributionWindow N
          (convolutionAutocorrelation f))
      atTop
      (𝓝 (completedPrimeContourRealizedFiniteWindowPairing f)) := by
  unfold completedPrimeContourRealizedFiniteWindowPairing
  exact
    finitePrimeContourRealizedTimeDistributionWindow_tendsto_timeDistributionPairing_ownerHorizontalDecay
      f

/-- The raw spectral contour scalar agrees with the completed finite-window contour scalar.

This compatibility wrapper consumes the split prime owner theorem
`completedPrimeContourFiniteWindowExpansion_diagonalDebtAbsorption_eq_GNSHeartScalar`
followed by the raw spectral/two-face comparison;
it is not a coordinate-summability statement. -/
theorem completedPrimeContourRealizedFiniteWindowPairing_eq_rawSpectralContourPairing_ownerTomography
    (f : ZetaAdmissibleFunction) :
    completedPrimeContourRealizedFiniteWindowPairing f =
      completedPrimeContourRealizedTimeDistributionPairing
        (convolutionAutocorrelation f) := by
  exact completedPrimeContourFiniteWindowGNSRealization_rawSpectral f

/-- The finite contour window minus the finite time window is the finite coordinate
remainder window. -/
theorem finitePrimeContourWindow_sub_finiteTimeWindow_eq_remainderWindow_ownerTomography
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    finitePrimeContourRealizedTimeDistributionWindow N
        (convolutionAutocorrelation f) -
      finitePrimeTimeDistributionWindow N (convolutionAutocorrelation f) =
        finitePrimeContourTransportCoordinateRemainderWindow N f := by
  exact
    (finitePrimeContourTransportCoordinateRemainderWindow_eq_contourWindow_sub_timeWindow
      N f).symm

/-- Completed finite-window prime transport: the time-side completed prime pairing is the
completed finite-window contour scalar.

This is a uniqueness-of-limits theorem for the finite-window triangle.  The finite
time-side windows converge to the completed time pairing, the finite contour windows
converge to the completed finite-window contour scalar, and their difference is the finite
coordinate remainder window killed by horizontal decay. -/
theorem completedPrimeTimeDistributionPairing_eq_completedContourFiniteWindowPairing_ownerTomographyLimit
    (f : ZetaAdmissibleFunction) :
    completedPrimeTimeDistributionPairing (convolutionAutocorrelation f) =
      completedPrimeContourRealizedFiniteWindowPairing f := by
  have htime :
      Tendsto
        (fun N : ℕ =>
          finitePrimeTimeDistributionWindow N (convolutionAutocorrelation f))
        atTop
        (𝓝 (completedPrimeTimeDistributionPairing (convolutionAutocorrelation f))) :=
    finitePrimeTimeDistributionWindow_tendsto_completedTimePairing_ownerTomography f
  have hcontour :
      Tendsto
        (fun N : ℕ =>
          finitePrimeContourRealizedTimeDistributionWindow N
            (convolutionAutocorrelation f))
        atTop
        (𝓝 (completedPrimeContourRealizedFiniteWindowPairing f)) :=
    finitePrimeContourRealizedTimeDistributionWindow_tendsto_completedFiniteWindowPairing_ownerTomography
      f
  have hremainder :
      Tendsto
        (fun N : ℕ => finitePrimeContourTransportCoordinateRemainderWindow N f)
        atTop
        (𝓝 0) :=
    finitePrimeContourTransportCoordinateRemainderWindow_tendsto_zero_ownerHorizontalDecay
      f
  have hwindowEq :
      (fun N : ℕ =>
        finitePrimeContourRealizedTimeDistributionWindow N
            (convolutionAutocorrelation f) -
          finitePrimeTimeDistributionWindow N (convolutionAutocorrelation f)) =
        (fun N : ℕ => finitePrimeContourTransportCoordinateRemainderWindow N f) := by
    funext N
    exact finitePrimeContourWindow_sub_finiteTimeWindow_eq_remainderWindow_ownerTomography
      N f
  exact
    completedWindowLimits_eq_of_sub_tendsto_zero
      htime
      hcontour
      hwindowEq
      hremainder

/-- Finite contour-realized prime windows converge to the raw completed contour-realized
prime pairing after comparing the raw spectral scalar with the completed finite-window
scalar.  The comparison is supplied by the split finite-window-to-raw-spectral theorem. -/
theorem finitePrimeContourRealizedTimeDistributionWindow_tendsto_completedContourRealizedTimeDistributionPairing_ownerTomography
    (f : ZetaAdmissibleFunction) :
    Tendsto
      (fun N : ℕ =>
        finitePrimeContourRealizedTimeDistributionWindow N
          (convolutionAutocorrelation f))
      atTop
      (𝓝
        (completedPrimeContourRealizedTimeDistributionPairing
          (convolutionAutocorrelation f))) := by
  have hfinite :
      Tendsto
        (fun N : ℕ =>
          finitePrimeContourRealizedTimeDistributionWindow N
            (convolutionAutocorrelation f))
        atTop
        (𝓝 (completedPrimeContourRealizedFiniteWindowPairing f)) :=
    finitePrimeContourRealizedTimeDistributionWindow_tendsto_completedFiniteWindowPairing_ownerTomography
      f
  have hcompare :
      completedPrimeContourRealizedFiniteWindowPairing f =
        completedPrimeContourRealizedTimeDistributionPairing
          (convolutionAutocorrelation f) :=
    completedPrimeContourRealizedFiniteWindowPairing_eq_rawSpectralContourPairing_ownerTomography
      f
  exact Eq.subst
    (motive := fun x : ℝ =>
      Tendsto
        (fun N : ℕ =>
          finitePrimeContourRealizedTimeDistributionWindow N
            (convolutionAutocorrelation f))
        atTop
        (𝓝 x))
    hcompare
    hfinite

/-- Raw spectral contour comparison wrapper.

The core finite-window transport theorem targets
`completedPrimeContourRealizedFiniteWindowPairing`.  Passing from that finite-window scalar
to the raw spectral presentation is supplied by
`completedPrimeContourFiniteWindowExpansion_diagonalDebtAbsorption_eq_GNSHeartScalar`
and the raw spectral/two-face comparison. -/
theorem completedPrimeTimeDistributionPairing_eq_contourRealizedPrimeChannel_ownerTomographyLimit
    (f : ZetaAdmissibleFunction) :
    completedPrimeTimeDistributionPairing (convolutionAutocorrelation f) =
      completedPrimeContourRealizedTimeDistributionPairing
        (convolutionAutocorrelation f) := by
  have hfinite :
      completedPrimeTimeDistributionPairing (convolutionAutocorrelation f) =
        completedPrimeContourRealizedFiniteWindowPairing f :=
    completedPrimeTimeDistributionPairing_eq_completedContourFiniteWindowPairing_ownerTomographyLimit
      f
  have hraw :
      completedPrimeContourRealizedFiniteWindowPairing f =
        completedPrimeContourRealizedTimeDistributionPairing
          (convolutionAutocorrelation f) :=
    completedPrimeContourRealizedFiniteWindowPairing_eq_rawSpectralContourPairing_ownerTomography
      f
  exact hfinite.trans hraw

/-- The completed contour-realized prime channel is the completed spectral prime channel. -/
theorem completedPrimeContourRealized_convolutionAutocorrelation_eq_completedSpectralPrimeChannel_ownerTomography
    (f : ZetaAdmissibleFunction) :
    completedPrimeContourRealizedTimeDistributionPairing
        (convolutionAutocorrelation f) =
      completedSpectralPrimeOffDiagonalChannel f := by
  have hrealized :
      completedPrimeContourRealizedTimeDistributionPairing
          (convolutionAutocorrelation f) =
        completedPrimeSpectralDistributionPairing
          (zetaCompletedSpectralLaplaceTransform (convolutionAutocorrelation f)) :=
    completedPrimeContourRealizedTimeDistribution_eq_spectralPrimePowerContribution
      (convolutionAutocorrelation f)
  have hspectral :
      completedSpectralPrimeOffDiagonalChannel f =
        completedPrimeSpectralDistributionPairing
          (zetaCompletedSpectralLaplaceTransform (convolutionAutocorrelation f)) :=
    completedSpectralPrimeOffDiagonalChannel_eq_spectralDistributionPairing f
  exact hrealized.trans hspectral.symm

/-- Global prime tomography: the completed raw off-diagonal channel is the real part of the
completed two-face/GNS boundary coefficient.

This is not a pointwise coordinate identification.  The coordinate owner theorem proves
that the completed two-face coordinate sum reconstructs the coefficient; this theorem owns
the global transport from the raw time-side completed channel to that reconstructed
two-face object. -/
theorem completedPrimeOffDiagonalChannel_eq_completedPrimeTwoFaceGNSBoundaryCoefficient_re_ownerTomography
    (f : ZetaAdmissibleFunction) :
    completedPrimeOffDiagonalChannel f =
      Complex.re (zetaCompletedPrimeTwoFaceGNSBoundaryCoefficient f) := by
  exact
    completedPrimeOffDiagonalChannel_eq_completedTwoFaceGNSBoundaryCoefficient_re_ownerDistributionTransport
      f

/-- A completed prime tomography class records the scalar seen after the completed prime
time-side boundary distribution is reconstructed as a two-face boundary object.

This is intentionally a global object.  Its scalar is not a pointwise coordinate
identification between real/log samples and spectral samples. -/
structure CompletedPrimeTomographyClass where
  scalar : ℝ

/-- The scalar carried by a completed prime tomography class. -/
def completedPrimeTomographyClassScalar
    (C : CompletedPrimeTomographyClass) : ℝ :=
  C.scalar

/-- Prime tomography classes are determined by their completed scalar. -/
theorem CompletedPrimeTomographyClass.ext_scalar
    {C D : CompletedPrimeTomographyClass}
    (hscalar :
      completedPrimeTomographyClassScalar C =
        completedPrimeTomographyClassScalar D) :
    C = D := by
  cases C with
  | mk c =>
    cases D with
    | mk d =>
      change { scalar := c } = ({ scalar := d } : CompletedPrimeTomographyClass)
      change c = d at hscalar
      exact congrArg (fun x : ℝ => ({ scalar := x } : CompletedPrimeTomographyClass))
        hscalar

/-- The completed time-side prime tomography projection: the raw completed time-side prime
distribution of the autocorrelation source. -/
noncomputable def completedPrimeTimeTomographyProjection
    (f : ZetaAdmissibleFunction) : ℝ :=
  completedPrimeTimeDistributionPairing (convolutionAutocorrelation f)

/-- The completed two-face prime tomography projection: the real part of the completed
two-face boundary coefficient. -/
noncomputable def completedPrimeTwoFaceTomographyProjection
    (f : ZetaAdmissibleFunction) : ℝ :=
  Complex.re (zetaCompletedPrimeTwoFaceGNSBoundaryCoefficient f)

/-- The completed time-side prime tomography class. -/
noncomputable def completedPrimeTimeTomographyClass
    (f : ZetaAdmissibleFunction) :
    CompletedPrimeTomographyClass where
  scalar := completedPrimeTimeTomographyProjection f

/-- The completed reconstructed two-face prime tomography class. -/
noncomputable def completedPrimeTwoFaceTomographyClass
    (f : ZetaAdmissibleFunction) :
    CompletedPrimeTomographyClass where
  scalar := completedPrimeTwoFaceTomographyProjection f

/-- The scalar of the completed time-side prime tomography class is the time projection. -/
theorem completedPrimeTomographyClassScalar_time
    (f : ZetaAdmissibleFunction) :
    completedPrimeTomographyClassScalar
        (completedPrimeTimeTomographyClass f) =
      completedPrimeTimeTomographyProjection f := by
  rfl

/-- The scalar of the completed two-face prime tomography class is the two-face projection. -/
theorem completedPrimeTomographyClassScalar_twoFace
    (f : ZetaAdmissibleFunction) :
    completedPrimeTomographyClassScalar
        (completedPrimeTwoFaceTomographyClass f) =
      completedPrimeTwoFaceTomographyProjection f := by
  rfl

/-- The completed time tomography projection is the completed time-side prime distribution. -/
theorem completedPrimeTimeTomographyProjection_eq_timeDistributionPairing
    (f : ZetaAdmissibleFunction) :
    completedPrimeTimeTomographyProjection f =
      completedPrimeTimeDistributionPairing (convolutionAutocorrelation f) := by
  rfl

/-- The completed two-face tomography projection is the completed contour-realized prime
distribution. -/
theorem completedPrimeTwoFaceTomographyProjection_eq_contourRealizedPairing
    (f : ZetaAdmissibleFunction) :
    completedPrimeTwoFaceTomographyProjection f =
      completedPrimeContourRealizedTimeDistributionPairing
        (convolutionAutocorrelation f) := by
  have hspectral :
      completedPrimeContourRealizedTimeDistributionPairing
          (convolutionAutocorrelation f) =
        completedPrimeSpectralDistributionPairing
          (zetaCompletedSpectralLaplaceTransform (convolutionAutocorrelation f)) :=
    completedPrimeContourRealizedTimeDistribution_eq_spectralPrimePowerContribution
      (convolutionAutocorrelation f)
  have hspectralChannel :
      completedSpectralPrimeOffDiagonalChannel f =
        completedPrimeSpectralDistributionPairing
          (zetaCompletedSpectralLaplaceTransform (convolutionAutocorrelation f)) :=
    completedSpectralPrimeOffDiagonalChannel_eq_spectralDistributionPairing f
  have hcoefficient :
      completedSpectralPrimeOffDiagonalChannel f =
        completedPrimeTwoFaceTomographyProjection f := by
    unfold completedPrimeTwoFaceTomographyProjection
    exact completedSpectralPrimeOffDiagonalChannel_eq_completedTwoFaceBoundaryCoefficient_re
      f
  exact (hspectral.trans (hspectralChannel.symm.trans hcoefficient)).symm

/-- Prime contour windows converge to the completed time-side prime distribution through the
horizontal-decay transport route.

This is the completed-window convergence theorem downstream code should use when it only
needs the honest contour-window limit.  It deliberately targets the time-side completed
prime distribution; comparison with the spectral two-face coefficient is a separate
tomography theorem. -/
theorem finitePrimeContourRealizedTimeDistributionWindow_tendsto_timeDistributionPairing_ownerTomography
    (f : ZetaAdmissibleFunction) :
    Tendsto
      (fun N : ℕ =>
        finitePrimeContourRealizedTimeDistributionWindow N
          (convolutionAutocorrelation f))
      atTop
      (𝓝 (completedPrimeTimeDistributionPairing (convolutionAutocorrelation f))) := by
  exact
    finitePrimeContourRealizedTimeDistributionWindow_tendsto_timeDistributionPairing_ownerHorizontalDecay
      f

/-- The completed time-side two-face coordinate sum reconstructs the completed two-face
boundary coefficient.

This is the prime holographic reconstruction root: the completed real time-side coordinate
sum and the completed spectral/two-face boundary coefficient are the same reconstructed
prime boundary scalar. -/
theorem completedPrimeTwoFaceBoundaryRealCoordinate_tsum_eq_coefficient_re_ownerTomography
    (f : ZetaAdmissibleFunction) :
    (∑' ι : ZetaPrimePowerIndex,
        completedPrimeTwoFaceGNSBoundaryRealCoordinate ι f) =
      Complex.re (zetaCompletedPrimeTwoFaceGNSBoundaryCoefficient f) := by
  exact completedPrimeTwoFaceBoundaryRealCoordinate_tsum_eq_coefficient_re_ownerCoordinates
    f

/-- Completed prime holographic scalar reconstruction.

The completed prime time-side projection and the completed two-face boundary projection
give the same reconstructed prime scalar.  This is the global reconstruction theorem: it
is not a pointwise identification between a time-side real/log coordinate and a vertical
or Laplace spectral sample. -/
theorem completedPrimeTimeTomographyProjection_eq_twoFaceTomographyProjection_ownerTomography
    (f : ZetaAdmissibleFunction) :
    completedPrimeTimeTomographyProjection f =
      completedPrimeTwoFaceTomographyProjection f := by
  unfold completedPrimeTimeTomographyProjection
  unfold completedPrimeTwoFaceTomographyProjection
  have htime :
      completedPrimeTimeDistributionPairing (convolutionAutocorrelation f) =
        completedPrimeOffDiagonalChannel f :=
    completedPrimeTimeDistributionPairing_eq_completedPrimeOffDiagonalChannel f
  have hcoefficient :
      completedPrimeOffDiagonalChannel f =
        Complex.re (zetaCompletedPrimeTwoFaceGNSBoundaryCoefficient f) :=
    completedPrimeOffDiagonalChannel_eq_completedPrimeTwoFaceGNSBoundaryCoefficient_re_ownerTomography f
  exact htime.trans hcoefficient

/-- Completed prime contour transport identifies the completed time-side prime distribution
with the completed contour-realized distribution.

This is the owner transport theorem for prime tomography.  It is the completed limit of
the finite contour-transport reconstruction, not a coordinatewise identification between
real-lag samples and spectral samples. -/
theorem completedPrimeTimeDistributionPairing_eq_contourRealizedPrimeChannel_ownerTransport
    (f : ZetaAdmissibleFunction) :
    completedPrimeTimeDistributionPairing (convolutionAutocorrelation f) =
      completedPrimeContourRealizedTimeDistributionPairing
        (convolutionAutocorrelation f) := by
  exact completedPrimeTimeDistributionPairing_eq_contourRealizedPrimeChannel_ownerTomographyLimit
    f

/-- Completed prime holographic reconstruction.

The completed prime time-side projection and the completed two-face boundary projection
define the same prime tomography class.  This is the class-valued wrapper over the scalar
reconstruction theorem. -/
theorem completedPrimeTimeTomographyClass_eq_twoFaceTomographyClass_ownerTomography
    (f : ZetaAdmissibleFunction) :
    completedPrimeTimeTomographyClass f =
      completedPrimeTwoFaceTomographyClass f := by
  exact CompletedPrimeTomographyClass.ext_scalar
    (calc
      completedPrimeTomographyClassScalar
          (completedPrimeTimeTomographyClass f) =
          completedPrimeTimeTomographyProjection f := by
        exact completedPrimeTomographyClassScalar_time f
      _ = completedPrimeTwoFaceTomographyProjection f := by
        exact completedPrimeTimeTomographyProjection_eq_twoFaceTomographyProjection_ownerTomography f
      _ =
          completedPrimeTomographyClassScalar
            (completedPrimeTwoFaceTomographyClass f) := by
        exact (completedPrimeTomographyClassScalar_twoFace f).symm)

/-- Completed prime channel tomography.

The completed physical time-side prime channel and the completed spectral/two-face prime
channel are the same reconstructed boundary object.  This is a global completed-channel
statement, not a pointwise equality between real-lag coordinates and spectral samples. -/
theorem completedPrimeOffDiagonalChannel_eq_completedSpectralPrimeOffDiagonalChannel_ownerTomography
    (f : ZetaAdmissibleFunction) :
    completedPrimeOffDiagonalChannel f =
      completedSpectralPrimeOffDiagonalChannel f := by
  exact
    completedPrimeOffDiagonalChannel_eq_completedSpectralPrimeOffDiagonalChannel_ownerDistributionTransport
      f

/-- Completed prime holographic reconstruction.

The completed prime time-side projection and the completed two-face boundary projection
define the same prime tomography class.  This is the global reconstruction theorem: it is
not a pointwise identification between a time-side real/log coordinate and a vertical or
Laplace spectral sample. -/
theorem completedPrimeTimeTomographyClass_eq_twoFaceTomographyClass
    (f : ZetaAdmissibleFunction) :
    completedPrimeTimeTomographyClass f =
      completedPrimeTwoFaceTomographyClass f := by
  exact completedPrimeTimeTomographyClass_eq_twoFaceTomographyClass_ownerTomography f

/-- The scalar consequence of completed prime holographic reconstruction. -/
theorem completedPrimeTomographyProjection_reconstructs_twoFaceCoefficient
    (f : ZetaAdmissibleFunction) :
    completedPrimeTimeTomographyProjection f =
      completedPrimeTwoFaceTomographyProjection f := by
  exact completedPrimeTimeTomographyProjection_eq_twoFaceTomographyProjection_ownerTomography
    f

/-- Time-side completed prime tomography: the completed real prime distribution is the real
part of the completed two-face boundary coefficient.

This owns the time-side half of prime holography.  It is deliberately separated from the
contour-side spectral realization so the final contour-transport theorem is just a
comparison through the same reconstructed two-face coefficient. -/
theorem completedPrimeTimeDistributionPairing_eq_completedTwoFaceBoundaryCoefficient_re_ownerTomography
    (f : ZetaAdmissibleFunction) :
    completedPrimeTimeDistributionPairing (convolutionAutocorrelation f) =
      Complex.re (zetaCompletedPrimeTwoFaceGNSBoundaryCoefficient f) := by
  have hchannel :
      completedPrimeTimeDistributionPairing (convolutionAutocorrelation f) =
        completedPrimeOffDiagonalChannel f :=
    completedPrimeTimeDistributionPairing_eq_completedPrimeOffDiagonalChannel f
  have hcoefficient :
      completedPrimeOffDiagonalChannel f =
        Complex.re (zetaCompletedPrimeTwoFaceGNSBoundaryCoefficient f) :=
    completedPrimeOffDiagonalChannel_eq_completedPrimeTwoFaceGNSBoundaryCoefficient_re_ownerTomography f
  exact hchannel.trans hcoefficient

/-- Contour-side completed prime tomography: the contour-realized prime distribution is the
real part of the completed two-face boundary coefficient. -/
theorem completedPrimeContourRealizedTimeDistributionPairing_eq_completedTwoFaceBoundaryCoefficient_re
    (f : ZetaAdmissibleFunction) :
    completedPrimeContourRealizedTimeDistributionPairing
        (convolutionAutocorrelation f) =
      Complex.re (zetaCompletedPrimeTwoFaceGNSBoundaryCoefficient f) := by
  have hspectral :
      completedPrimeContourRealizedTimeDistributionPairing
          (convolutionAutocorrelation f) =
        completedPrimeSpectralDistributionPairing
          (zetaCompletedSpectralLaplaceTransform (convolutionAutocorrelation f)) :=
    completedPrimeContourRealizedTimeDistribution_eq_spectralPrimePowerContribution
      (convolutionAutocorrelation f)
  have hspectralChannel :
      completedSpectralPrimeOffDiagonalChannel f =
        completedPrimeSpectralDistributionPairing
          (zetaCompletedSpectralLaplaceTransform (convolutionAutocorrelation f)) :=
    completedSpectralPrimeOffDiagonalChannel_eq_spectralDistributionPairing f
  have hcoefficient :
      completedSpectralPrimeOffDiagonalChannel f =
        Complex.re (zetaCompletedPrimeTwoFaceGNSBoundaryCoefficient f) :=
    completedSpectralPrimeOffDiagonalChannel_eq_completedTwoFaceBoundaryCoefficient_re
      f
  exact hspectral.trans (hspectralChannel.symm.trans hcoefficient)

/-- Completed prime-channel tomography identifies the time-side completed prime distribution
with the contour-realized prime channel.

The owner content is the two comparison theorems to the same completed two-face boundary
coefficient; this theorem is the algebraic gluing step between those two realized faces. -/
theorem completedPrimeTimeDistributionPairing_eq_contourRealizedPrimeChannel_ownerTomography
    (f : ZetaAdmissibleFunction) :
    completedPrimeTimeDistributionPairing (convolutionAutocorrelation f) =
      completedPrimeContourRealizedTimeDistributionPairing
        (convolutionAutocorrelation f) := by
  exact completedPrimeTimeDistributionPairing_eq_contourRealizedPrimeChannel_ownerTransport f

/-- Completed contour transport has no residual boundary difference.  This is the analytic
contour-realization theorem: after passing to the completed prime channel, the finite
horizontal/transport remainder has zero limit. -/
theorem completedPrimeContourTransportBoundaryDifference_eq_zero
    (f : ZetaAdmissibleFunction) :
    completedPrimeContourTransportBoundaryDifference f = 0 := by
  have htransport :
      completedPrimeTimeDistributionPairing (convolutionAutocorrelation f) =
        completedPrimeContourRealizedTimeDistributionPairing
          (convolutionAutocorrelation f) :=
    completedPrimeTimeDistributionPairing_eq_contourRealizedPrimeChannel_ownerTomography
      f
  unfold completedPrimeContourTransportBoundaryDifference
  let C : ℝ :=
    completedPrimeContourRealizedTimeDistributionPairing
      (convolutionAutocorrelation f)
  let T : ℝ :=
    completedPrimeTimeDistributionPairing (convolutionAutocorrelation f)
  change C - T = 0
  have hCT : C = T := htransport.symm
  calc
    C - T = T - T := by
      exact congrArg (fun x : ℝ => x - T) hCT
    _ = 0 := by
      exact sub_self T

/-- The finite contour-transport remainder vanishes in the completed prime realization. -/
theorem finitePrimeContourTransportRemainder_tendsto_zero
    (f : ZetaAdmissibleFunction) :
    Tendsto
      (fun N : ℕ => finitePrimeContourTransportRemainder N f)
      atTop
      (𝓝 0) := by
  exact finitePrimeContourTransportRemainder_tendsto_zero_ownerHorizontalDecay f

/-- Completed contour realization identifies the time-side prime distribution with its
contour-realized prime channel. -/
theorem completedPrimeTimeDistributionPairing_eq_contourRealizedPrimeChannel
    (f : ZetaAdmissibleFunction) :
    completedPrimeTimeDistributionPairing (convolutionAutocorrelation f) =
      completedPrimeContourRealizedTimeDistributionPairing
        (convolutionAutocorrelation f) := by
  exact completedPrimeTimeDistributionPairing_eq_contourRealizedPrimeChannel_ownerTomography
    f

/-- Completed contour realization identifies the real prime boundary channel with the
contour-realized prime channel. -/
theorem primeBoundaryChannel_convolutionAutocorrelation_re_eq_contourRealizedPrimeChannel
    (f : ZetaAdmissibleFunction) :
    Complex.re (primeBoundaryChannel (convolutionAutocorrelation f)) =
      completedPrimeContourRealizedTimeDistributionPairing
        (convolutionAutocorrelation f) := by
  have htime :
      Complex.re (primeBoundaryChannel (convolutionAutocorrelation f)) =
        completedPrimeTimeDistributionPairing (convolutionAutocorrelation f) := by
    have hprimePower :
        completedPrimeTimeDistributionPairing (convolutionAutocorrelation f) =
          Complex.re
            (zetaCompletedExplicitFormulaPrimePowerContribution
              (convolutionAutocorrelation f)) :=
      completedPrimeTimeDistributionPairing_eq_primePowerContribution_re
        (convolutionAutocorrelation f)
    have howner :
        zetaCompletedExplicitFormulaPrimePowerContribution
            (convolutionAutocorrelation f) =
          primeBoundaryChannel (convolutionAutocorrelation f) := by
      unfold primeBoundaryChannel
      exact zetaCompletedExplicitFormulaPrimePowerContribution_eq_primeContribution
        (convolutionAutocorrelation f)
    exact (congrArg Complex.re howner).symm.trans hprimePower.symm
  have hrealized :
      completedPrimeTimeDistributionPairing (convolutionAutocorrelation f) =
        completedPrimeContourRealizedTimeDistributionPairing
          (convolutionAutocorrelation f) :=
    completedPrimeTimeDistributionPairing_eq_contourRealizedPrimeChannel f
  exact htime.trans hrealized

/-- Completed contour realization turns the realized prime channel into the spectral-sample
prime channel. -/
theorem completedPrimeContourRealized_convolutionAutocorrelation_eq_completedSpectralPrimeChannel
    (f : ZetaAdmissibleFunction) :
    completedPrimeContourRealizedTimeDistributionPairing
        (convolutionAutocorrelation f) =
      completedSpectralPrimeOffDiagonalChannel f := by
  exact
    completedPrimeContourRealized_convolutionAutocorrelation_eq_completedSpectralPrimeChannel_ownerTomography
      f

/-- Completed contour realization identifies the time-side real prime channel with the
spectral-sample prime channel. -/
theorem primeBoundaryChannel_convolutionAutocorrelation_re_eq_completedSpectralPrimeChannel
    (f : ZetaAdmissibleFunction) :
    Complex.re (primeBoundaryChannel (convolutionAutocorrelation f)) =
      completedSpectralPrimeOffDiagonalChannel f := by
  have hprime :
      Complex.re (primeBoundaryChannel (convolutionAutocorrelation f)) =
        completedPrimeOffDiagonalChannel f :=
    (completedPrimeOffDiagonalChannel_eq_primeBoundaryChannel f).symm
  have htomography :
      completedPrimeOffDiagonalChannel f =
        completedSpectralPrimeOffDiagonalChannel f :=
    completedPrimeOffDiagonalChannel_eq_completedSpectralPrimeOffDiagonalChannel_ownerTomography
      f
  exact hprime.trans htomography

/-- Prime boundary tomography: the real explicit-formula prime channel of the completed
autocorrelation probe reconstructs the completed spectral two-face boundary coefficient.

This is the global contour/log-coordinate transport theorem.  It deliberately compares
completed channels, not pointwise real-lag and spectral coordinates. -/
theorem primeBoundaryChannel_convolutionAutocorrelation_re_eq_completedTwoFaceBoundaryCoefficient
    (f : ZetaAdmissibleFunction) :
    Complex.re (primeBoundaryChannel (convolutionAutocorrelation f)) =
      Complex.re (zetaCompletedPrimeTwoFaceGNSBoundaryCoefficient f) := by
  have hcontour :
      Complex.re (primeBoundaryChannel (convolutionAutocorrelation f)) =
        completedSpectralPrimeOffDiagonalChannel f :=
    primeBoundaryChannel_convolutionAutocorrelation_re_eq_completedSpectralPrimeChannel f
  have hspectral :
      completedSpectralPrimeOffDiagonalChannel f =
        Complex.re (zetaCompletedPrimeTwoFaceGNSBoundaryCoefficient f) :=
    completedSpectralPrimeOffDiagonalChannel_eq_completedTwoFaceBoundaryCoefficient_re f
  exact hcontour.trans hspectral

/-- Completed prime tomography: the time-side off-diagonal channel reconstructs the real
part of the completed spectral boundary coefficient. -/
theorem completedPrimeOffDiagonalChannel_eq_completedPrimeTwoFaceGNSBoundaryCoefficient_re
    (f : ZetaAdmissibleFunction) :
    completedPrimeOffDiagonalChannel f =
      Complex.re (zetaCompletedPrimeTwoFaceGNSBoundaryCoefficient f) := by
  exact completedPrimeOffDiagonalChannel_eq_completedPrimeTwoFaceGNSBoundaryCoefficient_re_ownerTomography
    f

/-- The completed sum of boundary real coordinates is the real part of the completed
boundary coefficient. -/
theorem completedPrimeTwoFaceGNSBoundaryRealCoordinate_tsum_eq_boundaryCoefficient_re
    (f : ZetaAdmissibleFunction) :
    (∑' ι : ZetaPrimePowerIndex,
        completedPrimeTwoFaceGNSBoundaryRealCoordinate ι f) =
      Complex.re (zetaCompletedPrimeTwoFaceGNSBoundaryCoefficient f) := by
  exact completedPrimeTwoFaceBoundaryRealCoordinate_tsum_eq_coefficient_re_ownerTomography f

/-- The completed sum of the reconstructed two-face/GNS boundary coordinates is the real part
of the completed prime two-face/GNS boundary coefficient.

This is the summability/real-part transport part of prime tomography.  The coordinate
reconstruction theorem owns the local analytic content; this theorem owns the completed
prime-power summation passage. -/
theorem completedPrimeTwoFaceGNSRealCoordinate_tsum_eq_matrixCoefficient_re
    (f : ZetaAdmissibleFunction) :
    (∑' ι : ZetaPrimePowerIndex,
        completedPrimeTwoFaceGNSBoundaryRealCoordinate ι f) =
      Complex.re (zetaCompletedPrimeTwoFaceGNSBoundaryCoefficient f) := by
  exact completedPrimeTwoFaceGNSBoundaryRealCoordinate_tsum_eq_boundaryCoefficient_re f

/-- Prime contour/tomographic realization: the raw time-side prime distribution of the
autocorrelation source realizes as the completed two-face prime coefficient.

This is the remaining prime presentation theorem.  It is not definitional: it is the
completed contour/log-coordinate transport identifying the raw prime distribution with its
completed spectral two-face presentation. -/
theorem completedPrimeTimeDistributionPairing_convolutionAutocorrelation_eq_completedTwoFace_re
    (f : ZetaAdmissibleFunction) :
    completedPrimeTimeDistributionPairing (convolutionAutocorrelation f) =
      Complex.re (zetaCompletedPrimeTwoFaceGNSBoundaryCoefficient f) := by
  exact completedPrimeTimeDistributionPairing_eq_completedTwoFaceBoundaryCoefficient_re_ownerTomography
    f

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
