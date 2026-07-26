import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaCompletedHilbertSource.ZetaCompletedWeightStream.ZetaCompletedFinitePart.ZetaCompletedSquareLedger.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaTransformCalculus.ZetaTransformCalculusBase.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaAdmissibleSpectralInterpolation.ZetaAdmissiblePaleyWiener.ZetaTransformCalculusWeighted.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaAdmissibleSpectralInterpolation.ZetaAdmissiblePaleyWiener.ZetaExplicitFormulaAnalyticCore.OwnerParts.Base
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaAdmissibleSpectralInterpolation.ZetaAdmissiblePaleyWiener.ZetaExplicitFormulaAnalyticCore.OwnerParts.BoundaryChannels
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaCompletedHilbertSource.ZetaPacketComparison.ZetaCompletedBoundaryDefect.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaCompletedHilbertSource.ZetaHermitianPacket.CompletedPrimePowerSampling

/-!
# Prime distribution transport

This file owns the prime time/spectral distribution objects used by the completed
boundary descent.  The later descent file consumes these definitions instead of
owning the prime distribution layer itself.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open Filter
open scoped Topology

namespace ZetaAdmissibleFunction

/-- The spectral boundary functional attached to a transform. -/
def spectralBoundaryChannel (Φ : ℂ → ℂ) : ℂ :=
  (∑ ℓ in zetaCompletedExplicitFormulaPrimeSupport,
    -((zetaCompletedExplicitFormulaPrimeWeight ℓ.1 ℓ.2 : ℂ) *
      Φ (zetaPrimePacketCenter ℓ.1 ℓ.2))) +
    (2 : ℂ) * Φ 0 +
    (1 / (1 / 2 : ℂ) + 1 / (1 - (1 / 2 : ℂ)))

/-- The windowed spectral prime channel over genuine prime-power indices. -/
def spectralPrimeBoundaryWindow
    (N : ℕ) (Φ : ℂ → ℂ) : ℂ :=
  ∑ ι in ZetaPrimePowerIndex.window N,
    -((ι.weight : ℂ) * Φ ι.center)

/-- The windowed completed spectral boundary channel over genuine prime-power indices. -/
def spectralCompletedBoundaryWindow
    (N : ℕ) (Φ : ℂ → ℂ) : ℂ :=
  spectralPrimeBoundaryWindow N Φ +
    (2 : ℂ) * Φ 0 +
    (1 / (1 / 2 : ℂ) + 1 / (1 - (1 / 2 : ℂ)))

/-- Spectral boundary compatibility with convolution-pair factorization. -/
theorem spectralBoundaryChannel_convolutionPair_factorization
    (f h : ZetaAdmissibleFunction) :
    spectralBoundaryChannel
        (zetaCompletedExplicitFormulaPhi (convolutionPair f h)) =
      spectralBoundaryChannel
        (fun z : ℂ =>
          zetaCompletedExplicitFormulaPhi f z *
            star (zetaCompletedExplicitFormulaPhi h (-star z))) := by
  unfold spectralBoundaryChannel
  have hprime :
      (∑ ℓ in zetaCompletedExplicitFormulaPrimeSupport,
          -((zetaCompletedExplicitFormulaPrimeWeight ℓ.1 ℓ.2 : ℂ) *
            zetaCompletedExplicitFormulaPhi (convolutionPair f h)
              (zetaPrimePacketCenter ℓ.1 ℓ.2))) =
        ∑ ℓ in zetaCompletedExplicitFormulaPrimeSupport,
          -((zetaCompletedExplicitFormulaPrimeWeight ℓ.1 ℓ.2 : ℂ) *
            (zetaCompletedExplicitFormulaPhi f (zetaPrimePacketCenter ℓ.1 ℓ.2) *
              star
                (zetaCompletedExplicitFormulaPhi h
                  (-star (zetaPrimePacketCenter ℓ.1 ℓ.2 : ℂ))))) := by
    exact Finset.sum_congr rfl
      (fun ℓ hℓ =>
        (fun hmem : ℓ ∈ zetaCompletedExplicitFormulaPrimeSupport =>
          by
            unfold zetaCompletedExplicitFormulaPhi
            unfold zetaAutocorrelationSpectralTransform
            exact congrArg
              (fun z : ℂ => -((zetaCompletedExplicitFormulaPrimeWeight ℓ.1 ℓ.2 : ℂ) * z))
              (Boundary.zetaLaplaceTransform_convolutionPair
                f h (zetaPrimePacketCenter ℓ.1 ℓ.2))) hℓ)
  have harch :
      (2 : ℂ) * zetaCompletedExplicitFormulaPhi (convolutionPair f h) 0 =
        (2 : ℂ) *
          (zetaCompletedExplicitFormulaPhi f 0 *
            star (zetaCompletedExplicitFormulaPhi h (-star (0 : ℂ)))) := by
    unfold zetaCompletedExplicitFormulaPhi
    unfold zetaAutocorrelationSpectralTransform
    exact congrArg (fun z : ℂ => (2 : ℂ) * z)
      (Boundary.zetaLaplaceTransform_convolutionPair f h 0)
  exact congrArg₂
    (fun prime arch : ℂ =>
      prime + arch + (1 / (1 / 2 : ℂ) + 1 / (1 - (1 / 2 : ℂ))))
    hprime harch

/-- The windowed spectral prime channel of a convolution pair factors through the two seed
transforms. -/
theorem spectralPrimeBoundaryWindow_convolutionPair_factorization
    (N : ℕ) (f h : ZetaAdmissibleFunction) :
    spectralPrimeBoundaryWindow N
        (zetaCompletedExplicitFormulaPhi (convolutionPair f h)) =
      spectralPrimeBoundaryWindow N
        (fun z : ℂ =>
          zetaCompletedExplicitFormulaPhi f z *
            star (zetaCompletedExplicitFormulaPhi h (-star z))) := by
  unfold spectralPrimeBoundaryWindow
  exact Finset.sum_congr rfl
    (fun ι hι =>
      (fun hmem : ι ∈ ZetaPrimePowerIndex.window N =>
        by
          unfold zetaCompletedExplicitFormulaPhi
          unfold zetaAutocorrelationSpectralTransform
          exact congrArg (fun z : ℂ => -((ι.weight : ℂ) * z))
            (Boundary.zetaLaplaceTransform_convolutionPair f h ι.center)) hι)

/-- The completed physical prime off-diagonal channel, obtained as the finite-part limit of
physical autocorrelation-kernel prime windows. -/
noncomputable def completedPhysicalPrimeOffDiagonalChannel
    (f : ZetaAdmissibleFunction) : ℝ :=
  completedPrimeOffDiagonalChannel f

/-- The time-side prime distribution coordinate.  This uses the raw logarithmic boundary
value and then takes the real symmetrized prime contribution; it does not mention the
Laplace transform. -/
def completedPrimeTimeDistributionCoordinate
    (ι : ZetaPrimePowerIndex) (g : ZetaAdmissibleFunction) : ℝ :=
  -(ι.weight *
    Complex.re
      (zetaCompletedTimeBoundaryValue g ι.center +
        star (zetaCompletedTimeBoundaryValue g ι.center)))

/-- Nongenuine indices have zero time-side prime distribution coordinate. -/
theorem completedPrimeTimeDistributionCoordinate_eq_zero_of_not_isGenuine
    (ι : ZetaPrimePowerIndex) (g : ZetaAdmissibleFunction)
    (hι : ¬ ZetaPrimePowerIndex.IsGenuine ι) :
    completedPrimeTimeDistributionCoordinate ι g = 0 := by
  have hweight : ι.weight = 0 :=
    ZetaPrimePowerIndex.weight_eq_zero_of_not_isGenuine ι hι
  unfold completedPrimeTimeDistributionCoordinate
  calc
    -(ι.weight *
        Complex.re
          (zetaCompletedTimeBoundaryValue g ι.center +
            star (zetaCompletedTimeBoundaryValue g ι.center))) =
        -(0 *
          Complex.re
            (zetaCompletedTimeBoundaryValue g ι.center +
              star (zetaCompletedTimeBoundaryValue g ι.center))) := by
      exact congrArg
        (fun x : ℝ =>
          -(x *
            Complex.re
              (zetaCompletedTimeBoundaryValue g ι.center +
                star (zetaCompletedTimeBoundaryValue g ι.center))))
        hweight
    _ = -0 := by
      exact congrArg Neg.neg
        (zero_mul
          (Complex.re
            (zetaCompletedTimeBoundaryValue g ι.center +
              star (zetaCompletedTimeBoundaryValue g ι.center))))
    _ = 0 := by
      exact neg_zero

/-- The finite time-side prime distribution over a prime-power window. -/
def finitePrimeTimeDistributionWindow
    (N : ℕ) (g : ZetaAdmissibleFunction) : ℝ :=
  ∑ ι in ZetaPrimePowerIndex.window N,
    completedPrimeTimeDistributionCoordinate ι g

/-- The completed time-side prime distribution pairing. -/
noncomputable def completedPrimeTimeDistributionPairing
    (g : ZetaAdmissibleFunction) : ℝ :=
  ∑' ι : ZetaPrimePowerIndex,
    completedPrimeTimeDistributionCoordinate ι g

/-- The spectral-side completed prime distribution pairing attached to a Laplace transform. -/
noncomputable def completedPrimeSpectralDistributionPairing
    (Φ : ℂ → ℂ) : ℝ :=
  Complex.re
    (∑' ι : ZetaPrimePowerIndex,
      -((ι.weight : ℂ) * (Φ ι.center + star (Φ ι.center))))

/-- The prime distribution after completed contour realization.  This is not the raw
time-side value; it is the time face after the completed contour/log-coordinate realization
has been applied. -/
noncomputable def completedPrimeContourRealizedTimeDistributionPairing
    (g : ZetaAdmissibleFunction) : ℝ :=
  completedPrimeSpectralDistributionPairing
    (zetaCompletedSpectralLaplaceTransform g)

/-- The finite contour-realized prime distribution over a prime-power window. -/
def finitePrimeContourRealizedTimeDistributionWindow
    (N : ℕ) (g : ZetaAdmissibleFunction) : ℝ :=
  Complex.re
    (∑ ι in ZetaPrimePowerIndex.window N,
      -((ι.weight : ℂ) *
        (zetaCompletedSpectralLaplaceTransform g ι.center +
          star (zetaCompletedSpectralLaplaceTransform g ι.center))))

/-- The contour-realized prime distribution coordinate. -/
noncomputable def completedPrimeContourRealizedTimeDistributionCoordinate
    (ι : ZetaPrimePowerIndex) (g : ZetaAdmissibleFunction) : ℝ :=
  Complex.re
    (-((ι.weight : ℂ) *
      (zetaCompletedSpectralLaplaceTransform g ι.center +
        star (zetaCompletedSpectralLaplaceTransform g ι.center))))

/-- The complex spectral/Laplace coordinate whose real part is the contour-realized prime
distribution coordinate. -/
noncomputable def completedPrimeContourRealizedSpectralCoordinate
    (ι : ZetaPrimePowerIndex) (g : ZetaAdmissibleFunction) : ℂ :=
  -((ι.weight : ℂ) *
    (zetaCompletedSpectralLaplaceTransform g ι.center +
      star (zetaCompletedSpectralLaplaceTransform g ι.center)))

/-- The contour-realized real coordinate is the real part of the complex spectral/Laplace
coordinate. -/
theorem completedPrimeContourRealizedTimeDistributionCoordinate_eq_spectralCoordinate_re
    (ι : ZetaPrimePowerIndex) (g : ZetaAdmissibleFunction) :
    completedPrimeContourRealizedTimeDistributionCoordinate ι g =
      Complex.re (completedPrimeContourRealizedSpectralCoordinate ι g) := by
  rfl

/-- The contour-realized spectral/Laplace coordinate is the completed negative two-face
boundary coordinate. -/
theorem completedPrimeContourRealizedSpectralCoordinate_eq_neg_twoFaceBoundaryCoordinate
    (ι : ZetaPrimePowerIndex) (f : ZetaAdmissibleFunction) :
    completedPrimeContourRealizedSpectralCoordinate ι
        (convolutionAutocorrelation f) =
      -zetaCompletedPrimeTwoFaceGNSSymmetrizedCoordinate ι f := by
  have hΦ :
      zetaCompletedSpectralLaplaceTransform
          (convolutionAutocorrelation f) ι.center =
        zetaCompletedExplicitFormulaPhi
          (convolutionAutocorrelation f) ι.center := by
    exact
      (congrFun
        (zetaCompletedExplicitFormulaPhi_eq_spectralLaplaceTransform
          (convolutionAutocorrelation f))
        ι.center).symm
  calc
    completedPrimeContourRealizedSpectralCoordinate ι
        (convolutionAutocorrelation f) =
        -((ι.weight : ℂ) *
          (zetaCompletedSpectralLaplaceTransform
              (convolutionAutocorrelation f) ι.center +
            star (zetaCompletedSpectralLaplaceTransform
              (convolutionAutocorrelation f) ι.center))) := by
      rfl
    _ =
        -((ι.weight : ℂ) *
          (zetaCompletedExplicitFormulaPhi
              (convolutionAutocorrelation f) ι.center +
            star (zetaCompletedExplicitFormulaPhi
              (convolutionAutocorrelation f) ι.center))) := by
      exact congrArg
        (fun z : ℂ =>
          -((ι.weight : ℂ) * (z + star z)))
        hΦ
    _ = -zetaCompletedPrimeTwoFaceGNSSymmetrizedCoordinate ι f := by
      exact zetaCompletedPrimeSpectralSampleCoordinate_eq_neg_twoFaceBoundaryCoordinate
        ι f

/-- The completed symmetrized two-face coordinate is bounded by twice the spectral
coordinate majorant. -/
theorem norm_zetaCompletedPrimeTwoFaceGNSSymmetrizedCoordinate_le_two_spectralMajorant
    (ι : ZetaPrimePowerIndex) (f : ZetaAdmissibleFunction) :
    ‖zetaCompletedPrimeTwoFaceGNSSymmetrizedCoordinate ι f‖ ≤
      2 * zetaCompletedPrimeSpectralCoordinateMajorant ι f := by
  let C : ℂ := zetaCompletedPrimeTwoFaceGNSOrientedCoordinate ι f
  have hC :
      ‖C‖ ≤ zetaCompletedPrimeSpectralCoordinateMajorant ι f :=
    norm_zetaCompletedPrimeTwoFaceGNSOrientedCoordinate_le_spectralMajorant
      ι f
  have hsymm :
      ‖zetaCompletedPrimeTwoFaceGNSSymmetrizedCoordinate ι f‖ ≤
        ‖C‖ + ‖star C‖ := by
    unfold zetaCompletedPrimeTwoFaceGNSSymmetrizedCoordinate
    change ‖C + star C‖ ≤ ‖C‖ + ‖star C‖
    exact norm_add_le C (star C)
  have hstar : ‖star C‖ = ‖C‖ :=
    norm_star C
  have htwoC :
      ‖C‖ + ‖star C‖ = 2 * ‖C‖ := by
    calc
      ‖C‖ + ‖star C‖ = ‖C‖ + ‖C‖ := by
        exact congrArg (fun x : ℝ => ‖C‖ + x) hstar
      _ = 2 * ‖C‖ := by
        exact (two_mul ‖C‖).symm
  have htwo :
      2 * ‖C‖ ≤ 2 * zetaCompletedPrimeSpectralCoordinateMajorant ι f := by
    exact mul_le_mul_of_nonneg_left hC zero_le_two
  exact hsymm.trans (Eq.subst
    (motive := fun x : ℝ =>
      x ≤ 2 * zetaCompletedPrimeSpectralCoordinateMajorant ι f)
    htwoC.symm
    htwo)

/-- The contour-realized spectral/Laplace coordinate is bounded by twice the spectral
coordinate majorant. -/
theorem norm_completedPrimeContourRealizedSpectralCoordinate_le_two_spectralMajorant
    (ι : ZetaPrimePowerIndex) (f : ZetaAdmissibleFunction) :
    ‖completedPrimeContourRealizedSpectralCoordinate ι
        (convolutionAutocorrelation f)‖ ≤
      2 * zetaCompletedPrimeSpectralCoordinateMajorant ι f := by
  have hcoordinate :
      completedPrimeContourRealizedSpectralCoordinate ι
          (convolutionAutocorrelation f) =
        -zetaCompletedPrimeTwoFaceGNSSymmetrizedCoordinate ι f :=
    completedPrimeContourRealizedSpectralCoordinate_eq_neg_twoFaceBoundaryCoordinate
      ι f
  calc
    ‖completedPrimeContourRealizedSpectralCoordinate ι
        (convolutionAutocorrelation f)‖ =
        ‖-zetaCompletedPrimeTwoFaceGNSSymmetrizedCoordinate ι f‖ := by
      exact congrArg norm hcoordinate
    _ = ‖zetaCompletedPrimeTwoFaceGNSSymmetrizedCoordinate ι f‖ := by
      exact norm_neg (zetaCompletedPrimeTwoFaceGNSSymmetrizedCoordinate ι f)
    _ ≤ 2 * zetaCompletedPrimeSpectralCoordinateMajorant ι f := by
      exact
        norm_zetaCompletedPrimeTwoFaceGNSSymmetrizedCoordinate_le_two_spectralMajorant
          ι f

/-- The prime-center spectral localization majorant for the two real-axis seed faces.

This is the weighted sample-square form of `zetaCompletedPrimeSpectralCoordinateMajorant`;
it is the shape controlled by completed-boundary spectral localization at prime centers. -/
noncomputable def zetaCompletedPrimeCenterSpectralLocalizationMajorant
    (ι : ZetaPrimePowerIndex) (f : ZetaAdmissibleFunction) : ℝ :=
  zetaCompletedPrimePositiveWeightedSampleNormSq ι f +
    zetaCompletedPrimeOppositeWeightedSampleNormSq ι f

/-- The abstract amplitude majorant is exactly the weighted prime-center localization
majorant. -/
theorem zetaCompletedPrimeSpectralCoordinateMajorant_eq_centerLocalizationMajorant
    (ι : ZetaPrimePowerIndex) (f : ZetaAdmissibleFunction) :
    zetaCompletedPrimeSpectralCoordinateMajorant ι f =
      zetaCompletedPrimeCenterSpectralLocalizationMajorant ι f := by
  unfold zetaCompletedPrimeSpectralCoordinateMajorant
  unfold zetaCompletedPrimeCenterSpectralLocalizationMajorant
  exact congrArg₂ HAdd.hAdd
    (zetaCompletedPrimeSpectralAmplitudeIndex_norm_sq_eq_weightedSampleNormSq
      ι f)
    (zetaCompletedPrimeOppositeSpectralAmplitudeIndex_norm_sq_eq_weightedSampleNormSq
      ι f)

/-- Nongenuine prime-power indices have zero prime-center spectral localization majorant. -/
theorem zetaCompletedPrimeCenterSpectralLocalizationMajorant_eq_zero_of_not_isGenuine
    (ι : ZetaPrimePowerIndex) (f : ZetaAdmissibleFunction)
    (hι : ¬ ZetaPrimePowerIndex.IsGenuine ι) :
    zetaCompletedPrimeCenterSpectralLocalizationMajorant ι f = 0 := by
  have hweight : ZetaPrimePowerIndex.weight ι = 0 :=
    ZetaPrimePowerIndex.weight_eq_zero_of_not_isGenuine ι hι
  have hpos :
      zetaCompletedPrimePositiveWeightedSampleNormSq ι f = 0 := by
    unfold zetaCompletedPrimePositiveWeightedSampleNormSq
    exact Eq.trans
      (congrArg
        (fun x : ℝ =>
          x * ‖zetaCompletedPrimeHermitianSeedAmplitude ι.p ι.n f‖ ^ 2)
        hweight)
      (zero_mul (‖zetaCompletedPrimeHermitianSeedAmplitude ι.p ι.n f‖ ^ 2))
  have hopp :
      zetaCompletedPrimeOppositeWeightedSampleNormSq ι f = 0 := by
    unfold zetaCompletedPrimeOppositeWeightedSampleNormSq
    exact Eq.trans
      (congrArg
        (fun x : ℝ =>
          x * ‖zetaCompletedPrimeHermitianNegativeSeedAmplitude ι.p ι.n f‖ ^ 2)
        hweight)
      (zero_mul (‖zetaCompletedPrimeHermitianNegativeSeedAmplitude ι.p ι.n f‖ ^ 2))
  unfold zetaCompletedPrimeCenterSpectralLocalizationMajorant
  exact (congrArg₂ HAdd.hAdd hpos hopp).trans (add_zero 0)

/-- Nongenuine prime-power indices have zero positive weighted sample-square. -/
theorem zetaCompletedPrimePositiveWeightedSampleNormSq_eq_zero_of_not_isGenuine
    (ι : ZetaPrimePowerIndex) (f : ZetaAdmissibleFunction)
    (hι : ¬ ZetaPrimePowerIndex.IsGenuine ι) :
    zetaCompletedPrimePositiveWeightedSampleNormSq ι f = 0 := by
  have hweight : ZetaPrimePowerIndex.weight ι = 0 :=
    ZetaPrimePowerIndex.weight_eq_zero_of_not_isGenuine ι hι
  unfold zetaCompletedPrimePositiveWeightedSampleNormSq
  exact Eq.trans
    (congrArg
      (fun x : ℝ =>
        x * ‖zetaCompletedPrimeHermitianSeedAmplitude ι.p ι.n f‖ ^ 2)
      hweight)
    (zero_mul (‖zetaCompletedPrimeHermitianSeedAmplitude ι.p ι.n f‖ ^ 2))

/-- Rectangular boxes and genuine prime-power windows give the same positive weighted
sample-square sum, because nongenuine indices have zero completed prime weight. -/
theorem sum_box_zetaCompletedPrimePositiveWeightedSampleNormSq_eq_sum_window
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    (∑ ι in ZetaPrimePowerIndex.box N,
      zetaCompletedPrimePositiveWeightedSampleNormSq ι f) =
      ∑ ι in ZetaPrimePowerIndex.window N,
        zetaCompletedPrimePositiveWeightedSampleNormSq ι f := by
  exact
    ZetaPrimePowerIndex.sum_box_eq_sum_window_of_zero_not_isGenuine
      (fun ι : ZetaPrimePowerIndex =>
        zetaCompletedPrimePositiveWeightedSampleNormSq ι f)
      (fun ι hι =>
        zetaCompletedPrimePositiveWeightedSampleNormSq_eq_zero_of_not_isGenuine
          ι f hι)
      N

/-- Nongenuine prime-power indices have zero opposite weighted sample-square. -/
theorem zetaCompletedPrimeOppositeWeightedSampleNormSq_eq_zero_of_not_isGenuine
    (ι : ZetaPrimePowerIndex) (f : ZetaAdmissibleFunction)
    (hι : ¬ ZetaPrimePowerIndex.IsGenuine ι) :
    zetaCompletedPrimeOppositeWeightedSampleNormSq ι f = 0 := by
  have hweight : ZetaPrimePowerIndex.weight ι = 0 :=
    ZetaPrimePowerIndex.weight_eq_zero_of_not_isGenuine ι hι
  unfold zetaCompletedPrimeOppositeWeightedSampleNormSq
  exact Eq.trans
    (congrArg
      (fun x : ℝ =>
        x * ‖zetaCompletedPrimeHermitianNegativeSeedAmplitude ι.p ι.n f‖ ^ 2)
      hweight)
    (zero_mul (‖zetaCompletedPrimeHermitianNegativeSeedAmplitude ι.p ι.n f‖ ^ 2))

/-- The positive weighted prime-center sample-square is nonnegative. -/
theorem zetaCompletedPrimePositiveWeightedSampleNormSq_nonnegative
    (ι : ZetaPrimePowerIndex) (f : ZetaAdmissibleFunction) :
    0 ≤ zetaCompletedPrimePositiveWeightedSampleNormSq ι f := by
  unfold zetaCompletedPrimePositiveWeightedSampleNormSq
  exact mul_nonneg
    (ZetaPrimePowerIndex.weight_nonnegative ι)
    (sq_nonneg ‖zetaCompletedPrimeHermitianSeedAmplitude ι.p ι.n f‖)

/-- The opposite weighted prime-center sample-square is nonnegative. -/
theorem zetaCompletedPrimeOppositeWeightedSampleNormSq_nonnegative
    (ι : ZetaPrimePowerIndex) (f : ZetaAdmissibleFunction) :
    0 ≤ zetaCompletedPrimeOppositeWeightedSampleNormSq ι f := by
  unfold zetaCompletedPrimeOppositeWeightedSampleNormSq
  exact mul_nonneg
    (ZetaPrimePowerIndex.weight_nonnegative ι)
    (sq_nonneg ‖zetaCompletedPrimeHermitianNegativeSeedAmplitude ι.p ι.n f‖)

/-- The prime-center spectral localization majorant is nonnegative. -/
theorem zetaCompletedPrimeCenterSpectralLocalizationMajorant_nonnegative
    (ι : ZetaPrimePowerIndex) (f : ZetaAdmissibleFunction) :
    0 ≤ zetaCompletedPrimeCenterSpectralLocalizationMajorant ι f := by
  unfold zetaCompletedPrimeCenterSpectralLocalizationMajorant
  exact add_nonneg
    (zetaCompletedPrimePositiveWeightedSampleNormSq_nonnegative ι f)
    (zetaCompletedPrimeOppositeWeightedSampleNormSq_nonnegative ι f)

/-- The positive weighted sample-square is one face of the completed spectral-coordinate
majorant. -/
theorem zetaCompletedPrimePositiveWeightedSampleNormSq_le_spectralCoordinateMajorant
    (ι : ZetaPrimePowerIndex) (f : ZetaAdmissibleFunction) :
    zetaCompletedPrimePositiveWeightedSampleNormSq ι f ≤
      zetaCompletedPrimeSpectralCoordinateMajorant ι f := by
  have hpositive :
      zetaCompletedPrimePositiveWeightedSampleNormSq ι f =
        ‖zetaCompletedPrimeSpectralAmplitudeIndex ι f‖ ^ 2 :=
    (zetaCompletedPrimeSpectralAmplitudeIndex_norm_sq_eq_weightedSampleNormSq
      ι f).symm
  have hopposite_nonneg :
      0 ≤ ‖zetaCompletedPrimeOppositeSpectralAmplitudeIndex ι f‖ ^ 2 :=
    sq_nonneg ‖zetaCompletedPrimeOppositeSpectralAmplitudeIndex ι f‖
  unfold zetaCompletedPrimeSpectralCoordinateMajorant
  exact Eq.subst
    (motive := fun x : ℝ =>
      x ≤
        ‖zetaCompletedPrimeSpectralAmplitudeIndex ι f‖ ^ 2 +
          ‖zetaCompletedPrimeOppositeSpectralAmplitudeIndex ι f‖ ^ 2)
    hpositive.symm
    (le_add_of_nonneg_right hopposite_nonneg)

/-- Nongenuine indices have zero contour-realized prime distribution coordinate. -/
theorem completedPrimeContourRealizedTimeDistributionCoordinate_eq_zero_of_not_isGenuine
    (ι : ZetaPrimePowerIndex) (g : ZetaAdmissibleFunction)
    (hι : ¬ ZetaPrimePowerIndex.IsGenuine ι) :
    completedPrimeContourRealizedTimeDistributionCoordinate ι g = 0 := by
  have hweight : ι.weight = 0 :=
    ZetaPrimePowerIndex.weight_eq_zero_of_not_isGenuine ι hι
  unfold completedPrimeContourRealizedTimeDistributionCoordinate
  calc
    Complex.re
        (-((ι.weight : ℂ) *
          (zetaCompletedSpectralLaplaceTransform g ι.center +
            star (zetaCompletedSpectralLaplaceTransform g ι.center)))) =
        Complex.re
          (-((0 : ℂ) *
            (zetaCompletedSpectralLaplaceTransform g ι.center +
              star (zetaCompletedSpectralLaplaceTransform g ι.center)))) := by
      exact congrArg
        (fun x : ℝ =>
          Complex.re
            (-((x : ℂ) *
              (zetaCompletedSpectralLaplaceTransform g ι.center +
                star (zetaCompletedSpectralLaplaceTransform g ι.center)))))
        hweight
    _ = Complex.re (-(0 : ℂ)) := by
      exact congrArg (fun x : ℂ => Complex.re (-x))
        (zero_mul
          (zetaCompletedSpectralLaplaceTransform g ι.center +
            star (zetaCompletedSpectralLaplaceTransform g ι.center)))
    _ = Complex.re (0 : ℂ) := by
      exact congrArg Complex.re (neg_zero : -(0 : ℂ) = 0)
    _ = 0 := by
      exact Complex.zero_re

/-- The finite contour-realized prime window is the sum of its contour-realized
coordinates. -/
theorem finitePrimeContourRealizedTimeDistributionWindow_eq_sum_coordinate
    (N : ℕ) (g : ZetaAdmissibleFunction) :
    finitePrimeContourRealizedTimeDistributionWindow N g =
      ∑ ι in ZetaPrimePowerIndex.window N,
        completedPrimeContourRealizedTimeDistributionCoordinate ι g := by
  unfold finitePrimeContourRealizedTimeDistributionWindow
  unfold completedPrimeContourRealizedTimeDistributionCoordinate
  exact
    Complex.re_sum
      (ZetaPrimePowerIndex.window N)
      (fun ι : ZetaPrimePowerIndex =>
        -((ι.weight : ℂ) *
          (zetaCompletedSpectralLaplaceTransform g ι.center +
            star (zetaCompletedSpectralLaplaceTransform g ι.center))))

/-- At an autocorrelation probe, the time-side prime coordinate is the physical
off-diagonal coordinate. -/
theorem completedPrimeTimeDistributionCoordinate_convolutionAutocorrelation_eq_physical
    (ι : ZetaPrimePowerIndex) (f : ZetaAdmissibleFunction) :
    completedPrimeTimeDistributionCoordinate ι (convolutionAutocorrelation f) =
      zetaPrimeOffDiagonalCoordinate ι f := by
  unfold completedPrimeTimeDistributionCoordinate
  unfold zetaPrimeOffDiagonalCoordinate
  have htime :
      zetaCompletedTimeBoundaryValue (convolutionAutocorrelation f) ι.center =
        convolutionAutocorrelationKernel f ι.center :=
    zetaCompletedTimeBoundaryValue_convolutionAutocorrelation_eq_kernel f ι.center
  have hsum :
      Complex.re
          (zetaCompletedTimeBoundaryValue (convolutionAutocorrelation f) ι.center +
            star (zetaCompletedTimeBoundaryValue (convolutionAutocorrelation f) ι.center)) =
        2 * Complex.re (zetaSeedInner (zetaTranslate ι.center f) f) := by
    have htime_sum :
        zetaCompletedTimeBoundaryValue (convolutionAutocorrelation f) ι.center +
            star (zetaCompletedTimeBoundaryValue (convolutionAutocorrelation f) ι.center) =
          convolutionAutocorrelationKernel f ι.center +
            star (convolutionAutocorrelationKernel f ι.center) := by
      exact congrArg₂ HAdd.hAdd htime (congrArg star htime)
    have hneg :
        convolutionAutocorrelationKernel f (-ι.center) =
          star (convolutionAutocorrelationKernel f ι.center) :=
      convolutionAutocorrelationKernel_neg_eq_conj f ι.center
    have hpair :
        Complex.re
            (convolutionAutocorrelationKernel f ι.center +
              convolutionAutocorrelationKernel f (-ι.center)) =
          2 * Complex.re (zetaSeedInner (zetaTranslate ι.center f) f) :=
      convolutionAutocorrelationKernel_add_neg_eq_two_re_translateInner
        f ι.center
    calc
      Complex.re
          (zetaCompletedTimeBoundaryValue (convolutionAutocorrelation f) ι.center +
            star (zetaCompletedTimeBoundaryValue (convolutionAutocorrelation f) ι.center)) =
          Complex.re
            (convolutionAutocorrelationKernel f ι.center +
              star (convolutionAutocorrelationKernel f ι.center)) := by
        exact congrArg Complex.re htime_sum
      _ =
          Complex.re
            (convolutionAutocorrelationKernel f ι.center +
              convolutionAutocorrelationKernel f (-ι.center)) := by
        exact congrArg
          (fun z : ℂ => Complex.re
            (convolutionAutocorrelationKernel f ι.center + z))
          hneg.symm
      _ = 2 * Complex.re (zetaSeedInner (zetaTranslate ι.center f) f) := hpair
  calc
    -(ι.weight *
        Complex.re
          (zetaCompletedTimeBoundaryValue (convolutionAutocorrelation f) ι.center +
            star (zetaCompletedTimeBoundaryValue (convolutionAutocorrelation f) ι.center))) =
        -(ι.weight *
          (2 * Complex.re (zetaSeedInner (zetaTranslate ι.center f) f))) := by
      exact congrArg (fun x : ℝ => -(ι.weight * x)) hsum
    _ =
        -(2 * ι.weight *
          Complex.re (zetaSeedInner (zetaTranslate ι.center f) f)) := by
      have hmul :
          ι.weight * (2 * Complex.re (zetaSeedInner (zetaTranslate ι.center f) f)) =
            2 * ι.weight *
              Complex.re (zetaSeedInner (zetaTranslate ι.center f) f) := by
        calc
          ι.weight * (2 * Complex.re (zetaSeedInner (zetaTranslate ι.center f) f)) =
              (ι.weight * 2) *
                Complex.re (zetaSeedInner (zetaTranslate ι.center f) f) := by
            exact (mul_assoc ι.weight 2
              (Complex.re (zetaSeedInner (zetaTranslate ι.center f) f))).symm
          _ =
              (2 * ι.weight) *
                Complex.re (zetaSeedInner (zetaTranslate ι.center f) f) := by
            exact congrArg
              (fun x : ℝ =>
                x * Complex.re (zetaSeedInner (zetaTranslate ι.center f) f))
              (mul_comm ι.weight 2)
          _ =
              2 * ι.weight *
                Complex.re (zetaSeedInner (zetaTranslate ι.center f) f) := by
            rfl
      exact congrArg Neg.neg hmul

/-- The completed physical prime channel is the autocorrelation specialization of the
time-side completed prime distribution. -/
theorem completedPhysicalPrimeOffDiagonalChannel_eq_timeDistributionPairing
    (f : ZetaAdmissibleFunction) :
    completedPhysicalPrimeOffDiagonalChannel f =
      completedPrimeTimeDistributionPairing (convolutionAutocorrelation f) := by
  unfold completedPhysicalPrimeOffDiagonalChannel
  unfold completedPrimeOffDiagonalChannel
  unfold zetaCompletedPrimeOffDiagonalChannel
  unfold completedPrimeTimeDistributionPairing
  exact tsum_congr
    (fun ι : ZetaPrimePowerIndex =>
      (completedPrimeTimeDistributionCoordinate_convolutionAutocorrelation_eq_physical
        ι f).symm)

/-- The time-side prime distribution coordinates are summable at an autocorrelation probe. -/
theorem summable_completedPrimeTimeDistributionCoordinate_convolutionAutocorrelation
    (f : ZetaAdmissibleFunction) :
    Summable
      (fun ι : ZetaPrimePowerIndex =>
        completedPrimeTimeDistributionCoordinate ι (convolutionAutocorrelation f)) := by
  exact (summable_zetaPrimeOffDiagonalCoordinate f).congr
    (fun ι : ZetaPrimePowerIndex =>
      (completedPrimeTimeDistributionCoordinate_convolutionAutocorrelation_eq_physical
        ι f).symm)

/-- Completed prime contour realization has identical realized time and spectral faces. -/
theorem completedPrimeContourRealizedTimeDistribution_eq_spectralPrimePowerContribution
    (g : ZetaAdmissibleFunction) :
    completedPrimeContourRealizedTimeDistributionPairing g =
      completedPrimeSpectralDistributionPairing
        (zetaCompletedSpectralLaplaceTransform g) := by
  rfl

/-- The time-side prime distribution pairing is the real part of the owner prime-power
explicit-formula contribution.  This is bookkeeping after the owner prime channel is defined
on the time/log side. -/
theorem completedPrimeTimeDistributionPairing_eq_primePowerContribution_re
    (g : ZetaAdmissibleFunction) :
    completedPrimeTimeDistributionPairing g =
      Complex.re (zetaCompletedExplicitFormulaPrimePowerContribution g) := by
  unfold completedPrimeTimeDistributionPairing
  unfold completedPrimeTimeDistributionCoordinate
  unfold zetaCompletedExplicitFormulaPrimePowerContribution
  let r : ZetaPrimePowerIndex → ℝ :=
    fun ι : ZetaPrimePowerIndex =>
      -(ι.weight *
        Complex.re
          (zetaCompletedTimeBoundaryValue g ι.center +
            star (zetaCompletedTimeBoundaryValue g ι.center)))
  have hleft : (↑(∑' ι : ZetaPrimePowerIndex, r ι) : ℂ).re =
      ∑' ι : ZetaPrimePowerIndex, r ι :=
    Complex.ofReal_re (∑' ι : ZetaPrimePowerIndex, r ι)
  have hcoerceTsum :
      (↑(∑' ι : ZetaPrimePowerIndex, r ι) : ℂ).re =
        (∑' ι : ZetaPrimePowerIndex, (r ι : ℂ)).re :=
    congrArg Complex.re (Complex.ofReal_tsum r)
  have hcoordinate :
      (fun ι : ZetaPrimePowerIndex => (r ι : ℂ)) =
        fun ι : ZetaPrimePowerIndex =>
          -((ι.weight : ℂ) *
            (((zetaCompletedTimeBoundaryValue g ι.center +
              star (zetaCompletedTimeBoundaryValue g ι.center)).re : ℝ) : ℂ)) :=
    funext
      (fun ι : ZetaPrimePowerIndex =>
        calc
          (r ι : ℂ) =
              ((-(ι.weight *
                Complex.re
                  (zetaCompletedTimeBoundaryValue g ι.center +
                    star (zetaCompletedTimeBoundaryValue g ι.center)))) : ℝ) := by
                exact Eq.refl _
          _ =
              -(((ι.weight *
                Complex.re
                  (zetaCompletedTimeBoundaryValue g ι.center +
                    star (zetaCompletedTimeBoundaryValue g ι.center))) : ℝ) : ℂ) := by
                exact Complex.ofReal_neg
                  (ι.weight *
                    Complex.re
                      (zetaCompletedTimeBoundaryValue g ι.center +
                        star (zetaCompletedTimeBoundaryValue g ι.center)))
          _ =
              -((ι.weight : ℂ) *
                (((zetaCompletedTimeBoundaryValue g ι.center +
                  star (zetaCompletedTimeBoundaryValue g ι.center)).re : ℝ) : ℂ)) := by
                exact congrArg Neg.neg
                  (Complex.ofReal_mul ι.weight
                    (Complex.re
                      (zetaCompletedTimeBoundaryValue g ι.center +
                        star (zetaCompletedTimeBoundaryValue g ι.center)))))
  have hright :
      (∑' ι : ZetaPrimePowerIndex, (r ι : ℂ)).re =
        (∑' ι : ZetaPrimePowerIndex,
          -((ι.weight : ℂ) *
            (((zetaCompletedTimeBoundaryValue g ι.center +
              star (zetaCompletedTimeBoundaryValue g ι.center)).re : ℝ) : ℂ))).re :=
    congrArg (fun u : ZetaPrimePowerIndex → ℂ => (∑' ι, u ι).re) hcoordinate
  exact (hleft.symm.trans hcoerceTsum).trans hright

end ZetaAdmissibleFunction

end

end LFunctions
end Boundary
