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

/-- The completed off-diagonal channel is the `tsum` of the completed two-face boundary real
coordinates. -/
theorem completedPrimeOffDiagonalChannel_eq_twoFaceBoundaryRealCoordinate_tsum
    (f : ZetaAdmissibleFunction) :
    completedPrimeOffDiagonalChannel f =
      ∑' ι : ZetaPrimePowerIndex,
        completedPrimeTwoFaceGNSBoundaryRealCoordinate ι f := by
  unfold completedPrimeOffDiagonalChannel
  unfold zetaCompletedPrimeOffDiagonalChannel
  unfold completedPrimeTwoFaceGNSBoundaryRealCoordinate

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

/-- The completed time-side prime tomography projection: sum of reconstructed real
two-face boundary coordinates. -/
noncomputable def completedPrimeTimeTomographyProjection
    (f : ZetaAdmissibleFunction) : ℝ :=
  ∑' ι : ZetaPrimePowerIndex,
    completedPrimeTwoFaceGNSBoundaryRealCoordinate ι f

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
  unfold completedPrimeTimeTomographyProjection
  unfold completedPrimeTimeDistributionPairing
  exact tsum_congr
    (fun ι : ZetaPrimePowerIndex =>
      (completedPrimeTimeDistributionCoordinate_convolutionAutocorrelation_eq_twoFaceGNSRealCoordinate
        ι f).symm)

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
  have htime :
      Tendsto
        (fun N : ℕ =>
          finitePrimeContourRealizedTimeDistributionWindow N
            (convolutionAutocorrelation f))
        atTop
        (𝓝 (completedPrimeTimeDistributionPairing (convolutionAutocorrelation f))) :=
    finitePrimeContourRealizedTimeDistributionWindow_tendsto_timeDistributionPairing_ownerTomography
      f
  have hcontour :
      Tendsto
        (fun N : ℕ =>
          finitePrimeContourRealizedTimeDistributionWindow N
            (convolutionAutocorrelation f))
        atTop
        (𝓝
          (completedPrimeContourRealizedTimeDistributionPairing
            (convolutionAutocorrelation f))) :=
    finitePrimeContourRealizedTimeDistributionWindow_tendsto_completedContourRealized
      (convolutionAutocorrelation f)
  exact tendsto_nhds_unique htime hcontour

/-- Completed prime holographic scalar reconstruction.

The completed prime time-side projection and the completed two-face boundary projection
give the same reconstructed prime scalar.  This is the global reconstruction theorem: it
is not a pointwise identification between a time-side real/log coordinate and a vertical
or Laplace spectral sample. -/
theorem completedPrimeTimeTomographyProjection_eq_twoFaceTomographyProjection_ownerTomography
    (f : ZetaAdmissibleFunction) :
    completedPrimeTimeTomographyProjection f =
      completedPrimeTwoFaceTomographyProjection f := by
  have htime :
      completedPrimeTimeTomographyProjection f =
        completedPrimeTimeDistributionPairing (convolutionAutocorrelation f) :=
    completedPrimeTimeTomographyProjection_eq_timeDistributionPairing f
  have htransport :
      completedPrimeTimeDistributionPairing (convolutionAutocorrelation f) =
        completedPrimeContourRealizedTimeDistributionPairing
          (convolutionAutocorrelation f) :=
    completedPrimeTimeDistributionPairing_eq_contourRealizedPrimeChannel_ownerTransport f
  have htwoFace :
      completedPrimeTwoFaceTomographyProjection f =
        completedPrimeContourRealizedTimeDistributionPairing
          (convolutionAutocorrelation f) :=
    completedPrimeTwoFaceTomographyProjection_eq_contourRealizedPairing f
  exact htime.trans (htransport.trans htwoFace.symm)

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
  calc
    (∑' ι : ZetaPrimePowerIndex,
        completedPrimeTwoFaceGNSBoundaryRealCoordinate ι f) =
        completedPrimeTimeTomographyProjection f := by
      rfl
    _ = completedPrimeTwoFaceTomographyProjection f := by
      exact completedPrimeTimeTomographyProjection_eq_twoFaceTomographyProjection_ownerTomography f
    _ = Complex.re (zetaCompletedPrimeTwoFaceGNSBoundaryCoefficient f) := by
      rfl

/-- Completed prime channel tomography.

The completed physical time-side prime channel and the completed spectral/two-face prime
channel are the same reconstructed boundary object.  This is a global completed-channel
statement, not a pointwise equality between real-lag coordinates and spectral samples. -/
theorem completedPrimeOffDiagonalChannel_eq_completedSpectralPrimeOffDiagonalChannel_ownerTomography
    (f : ZetaAdmissibleFunction) :
    completedPrimeOffDiagonalChannel f =
      completedSpectralPrimeOffDiagonalChannel f := by
  have hchannel :
      completedPrimeOffDiagonalChannel f =
        ∑' ι : ZetaPrimePowerIndex,
          completedPrimeTwoFaceGNSBoundaryRealCoordinate ι f :=
    completedPrimeOffDiagonalChannel_eq_twoFaceBoundaryRealCoordinate_tsum f
  have hcoefficient :
      (∑' ι : ZetaPrimePowerIndex,
          completedPrimeTwoFaceGNSBoundaryRealCoordinate ι f) =
        Complex.re (zetaCompletedPrimeTwoFaceGNSBoundaryCoefficient f) :=
    completedPrimeTwoFaceBoundaryRealCoordinate_tsum_eq_coefficient_re_ownerTomography f
  have hspectral :
      completedSpectralPrimeOffDiagonalChannel f =
        Complex.re (zetaCompletedPrimeTwoFaceGNSBoundaryCoefficient f) :=
    completedSpectralPrimeOffDiagonalChannel_eq_completedTwoFaceBoundaryCoefficient_re
      f
  exact hchannel.trans (hcoefficient.trans hspectral.symm)

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
  unfold completedPrimeTimeTomographyProjection
  unfold completedPrimeTwoFaceTomographyProjection
  exact completedPrimeTwoFaceBoundaryRealCoordinate_tsum_eq_coefficient_re_ownerTomography
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
  have hsum :
      completedPrimeOffDiagonalChannel f =
        ∑' ι : ZetaPrimePowerIndex,
          completedPrimeTwoFaceGNSBoundaryRealCoordinate ι f :=
    completedPrimeOffDiagonalChannel_eq_twoFaceBoundaryRealCoordinate_tsum f
  have hcoefficient :
      (∑' ι : ZetaPrimePowerIndex,
          completedPrimeTwoFaceGNSBoundaryRealCoordinate ι f) =
        Complex.re (zetaCompletedPrimeTwoFaceGNSBoundaryCoefficient f) :=
    completedPrimeTwoFaceBoundaryRealCoordinate_tsum_eq_coefficient_re_ownerTomography
      f
  exact hchannel.trans (hsum.trans hcoefficient)

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
  have hsum :
      completedPrimeOffDiagonalChannel f =
        ∑' ι : ZetaPrimePowerIndex,
          completedPrimeTwoFaceGNSBoundaryRealCoordinate ι f :=
    completedPrimeOffDiagonalChannel_eq_twoFaceBoundaryRealCoordinate_tsum f
  have hcoefficient :
      (∑' ι : ZetaPrimePowerIndex,
          completedPrimeTwoFaceGNSBoundaryRealCoordinate ι f) =
        Complex.re (zetaCompletedPrimeTwoFaceGNSBoundaryCoefficient f) :=
    completedPrimeTwoFaceBoundaryRealCoordinate_tsum_eq_coefficient_re_ownerTomography
      f
  exact hsum.trans hcoefficient

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
  have hcoord :
      (fun ι : ZetaPrimePowerIndex =>
          completedPrimeTimeDistributionCoordinate ι
            (convolutionAutocorrelation f)) =
        (fun ι : ZetaPrimePowerIndex =>
          completedPrimeTwoFaceGNSBoundaryRealCoordinate ι f) := by
    funext ι
    exact
      completedPrimeTimeDistributionCoordinate_convolutionAutocorrelation_eq_twoFaceGNSRealCoordinate
        ι f
  unfold completedPrimeTimeDistributionPairing
  calc
    (∑' ι : ZetaPrimePowerIndex,
          completedPrimeTimeDistributionCoordinate ι
            (convolutionAutocorrelation f)) =
        ∑' ι : ZetaPrimePowerIndex,
          completedPrimeTwoFaceGNSBoundaryRealCoordinate ι f := by
      exact congrArg
        (fun u : ZetaPrimePowerIndex → ℝ =>
          ∑' ι : ZetaPrimePowerIndex, u ι)
        hcoord
    _ = Complex.re (zetaCompletedPrimeTwoFaceGNSBoundaryCoefficient f) :=
      completedPrimeTwoFaceGNSRealCoordinate_tsum_eq_matrixCoefficient_re f

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
