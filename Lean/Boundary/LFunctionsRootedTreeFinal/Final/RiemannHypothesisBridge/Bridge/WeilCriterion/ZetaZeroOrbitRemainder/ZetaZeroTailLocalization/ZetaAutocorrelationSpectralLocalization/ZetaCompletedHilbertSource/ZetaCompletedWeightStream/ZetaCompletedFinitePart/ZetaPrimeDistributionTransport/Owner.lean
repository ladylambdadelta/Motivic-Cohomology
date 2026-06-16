import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaCompletedHilbertSource.ZetaCompletedWeightStream.ZetaCompletedFinitePart.ZetaCompletedSquareLedger.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaTransformCalculus.ZetaTransformCalculusBase.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaAdmissibleSpectralInterpolation.ZetaAdmissiblePaleyWiener.ZetaTransformCalculusWeighted.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaAdmissibleSpectralInterpolation.ZetaAdmissiblePaleyWiener.ZetaExplicitFormulaAnalyticCore.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaCompletedHilbertSource.ZetaPacketComparison.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaCompletedHilbertSource.ZetaHermitianPacket.Owner

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
          (zetaCompletedExplicitFormulaPrimeWeight ℓ.1 ℓ.2 : ℂ) *
            zetaCompletedExplicitFormulaPhi (convolutionPair f h)
              (zetaPrimePacketCenter ℓ.1 ℓ.2)) =
        ∑ ℓ in zetaCompletedExplicitFormulaPrimeSupport,
          (zetaCompletedExplicitFormulaPrimeWeight ℓ.1 ℓ.2 : ℂ) *
            (zetaCompletedExplicitFormulaPhi f (zetaPrimePacketCenter ℓ.1 ℓ.2) *
              star
                (zetaCompletedExplicitFormulaPhi h
                  (-star (zetaPrimePacketCenter ℓ.1 ℓ.2 : ℂ)))) := by
    refine Finset.sum_congr rfl ?_
    intro ℓ hℓ
    unfold zetaCompletedExplicitFormulaPhi
    unfold zetaAutocorrelationSpectralTransform
    exact congrArg
      (fun z : ℂ => (zetaCompletedExplicitFormulaPrimeWeight ℓ.1 ℓ.2 : ℂ) * z)
      (Boundary.zetaLaplaceTransform_convolutionPair
        f h (zetaPrimePacketCenter ℓ.1 ℓ.2))
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
  refine Finset.sum_congr rfl ?_
  intro ι hι
  unfold zetaCompletedExplicitFormulaPhi
  unfold zetaAutocorrelationSpectralTransform
  exact congrArg (fun z : ℂ => (ι.weight : ℂ) * z)
    (Boundary.zetaLaplaceTransform_convolutionPair f h ι.center)

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
    exact mul_le_mul_of_nonneg_left hC (by norm_num : (0 : ℝ) ≤ 2)
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
      (zero_mul ‖zetaCompletedPrimeHermitianSeedAmplitude ι.p ι.n f‖ ^ 2)
  have hopp :
      zetaCompletedPrimeOppositeWeightedSampleNormSq ι f = 0 := by
    unfold zetaCompletedPrimeOppositeWeightedSampleNormSq
    exact Eq.trans
      (congrArg
        (fun x : ℝ =>
          x * ‖zetaCompletedPrimeHermitianNegativeSeedAmplitude ι.p ι.n f‖ ^ 2)
        hweight)
      (zero_mul ‖zetaCompletedPrimeHermitianNegativeSeedAmplitude ι.p ι.n f‖ ^ 2)
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
    (zero_mul ‖zetaCompletedPrimeHermitianSeedAmplitude ι.p ι.n f‖ ^ 2)

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
    (zero_mul ‖zetaCompletedPrimeHermitianNegativeSeedAmplitude ι.p ι.n f‖ ^ 2)

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

/-- The weighted prime-center sampling family for the completed autocorrelation spectral
transform. -/
noncomputable def completedAutocorrelationSpectralTransform_weightedPrimeSampling
    (ι : ZetaPrimePowerIndex) (f : ZetaAdmissibleFunction) : ℝ :=
  ZetaPrimePowerIndex.weight ι *
    ‖zetaCompletedSpectralLaplaceTransform f ι.center‖ ^ 2

/-- The prime-center Plancherel/localization density of the completed autocorrelation
spectral transform before inserting the explicit prime-power weight. -/
noncomputable def completedAutocorrelationSpectralTransform_primeCenterPlancherelDensity
    (ι : ZetaPrimePowerIndex) (f : ZetaAdmissibleFunction) : ℝ :=
  ‖zetaCompletedSpectralLaplaceTransform f ι.center‖ ^ 2

/-- The prime-center Plancherel/localization density is nonnegative. -/
theorem completedAutocorrelationSpectralTransform_primeCenterPlancherelDensity_nonnegative
    (ι : ZetaPrimePowerIndex) (f : ZetaAdmissibleFunction) :
    0 ≤
      completedAutocorrelationSpectralTransform_primeCenterPlancherelDensity
        ι f := by
  unfold completedAutocorrelationSpectralTransform_primeCenterPlancherelDensity
  exact sq_nonneg ‖zetaCompletedSpectralLaplaceTransform f ι.center‖

/-- Weighted prime sampling is the explicit prime-power weight times the completed
autocorrelation prime-center Plancherel/localization density. -/
theorem completedAutocorrelationSpectralTransform_weightedPrimeSampling_eq_weight_mul_density
    (ι : ZetaPrimePowerIndex) (f : ZetaAdmissibleFunction) :
    completedAutocorrelationSpectralTransform_weightedPrimeSampling ι f =
      ZetaPrimePowerIndex.weight ι *
        completedAutocorrelationSpectralTransform_primeCenterPlancherelDensity
          ι f := by
  unfold completedAutocorrelationSpectralTransform_weightedPrimeSampling
  unfold completedAutocorrelationSpectralTransform_primeCenterPlancherelDensity

/-- Weighted prime sampling is nonnegative. -/
theorem completedAutocorrelationSpectralTransform_weightedPrimeSampling_nonnegative
    (ι : ZetaPrimePowerIndex) (f : ZetaAdmissibleFunction) :
    0 ≤ completedAutocorrelationSpectralTransform_weightedPrimeSampling ι f := by
  have hweight : 0 ≤ ZetaPrimePowerIndex.weight ι :=
    ZetaPrimePowerIndex.weight_nonnegative ι
  have hdensity :
      0 ≤
        completedAutocorrelationSpectralTransform_primeCenterPlancherelDensity
          ι f :=
    completedAutocorrelationSpectralTransform_primeCenterPlancherelDensity_nonnegative
      ι f
  exact Eq.subst
    (motive := fun x : ℝ =>
      0 ≤ x)
    (completedAutocorrelationSpectralTransform_weightedPrimeSampling_eq_weight_mul_density
      ι f).symm
    (mul_nonneg hweight hdensity)

/-- Nongenuine prime-power indices have zero weighted prime sampling. -/
theorem completedAutocorrelationSpectralTransform_weightedPrimeSampling_eq_zero_of_not_isGenuine
    (ι : ZetaPrimePowerIndex) (f : ZetaAdmissibleFunction)
    (hι : ¬ ZetaPrimePowerIndex.IsGenuine ι) :
    completedAutocorrelationSpectralTransform_weightedPrimeSampling ι f = 0 := by
  have hweight : ZetaPrimePowerIndex.weight ι = 0 :=
    ZetaPrimePowerIndex.weight_eq_zero_of_not_isGenuine ι hι
  unfold completedAutocorrelationSpectralTransform_weightedPrimeSampling
  exact Eq.trans
    (congrArg
      (fun x : ℝ =>
        x * ‖zetaCompletedSpectralLaplaceTransform f ι.center‖ ^ 2)
      hweight)
    (zero_mul ‖zetaCompletedSpectralLaplaceTransform f ι.center‖ ^ 2)

/-- Rectangular boxes and genuine prime-power windows give the same weighted prime-sampling
sum, because nongenuine indices have zero completed prime weight. -/
theorem sum_box_completedAutocorrelationSpectralTransform_weightedPrimeSampling_eq_sum_window
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    (∑ ι in ZetaPrimePowerIndex.box N,
      completedAutocorrelationSpectralTransform_weightedPrimeSampling ι f) =
      ∑ ι in ZetaPrimePowerIndex.window N,
        completedAutocorrelationSpectralTransform_weightedPrimeSampling ι f := by
  exact
    ZetaPrimePowerIndex.sum_box_eq_sum_window_of_zero_not_isGenuine
      (fun ι : ZetaPrimePowerIndex =>
        completedAutocorrelationSpectralTransform_weightedPrimeSampling ι f)
      (fun ι hι =>
        completedAutocorrelationSpectralTransform_weightedPrimeSampling_eq_zero_of_not_isGenuine
          ι f hι)
      N

/-- The finite weighted prime-power sampling mass of the completed autocorrelation spectral
transform over the genuine prime-power window. -/
noncomputable def completedAutocorrelationSpectralTransform_weightedPrimeSamplingWindow
    (N : ℕ) (f : ZetaAdmissibleFunction) : ℝ :=
  ∑ ι in ZetaPrimePowerIndex.window N,
    completedAutocorrelationSpectralTransform_weightedPrimeSampling ι f

/-- The weighted prime-power sampling window unfolds to the finite genuine-window sum. -/
theorem completedAutocorrelationSpectralTransform_weightedPrimeSamplingWindow_eq_sum
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    completedAutocorrelationSpectralTransform_weightedPrimeSamplingWindow N f =
      ∑ ι in ZetaPrimePowerIndex.window N,
        completedAutocorrelationSpectralTransform_weightedPrimeSampling ι f := by
  rfl

/-- The rectangular box sampling sum equals the genuine weighted prime-power sampling
window. -/
theorem sum_box_completedAutocorrelationSpectralTransform_weightedPrimeSampling_eq_window
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    (∑ ι in ZetaPrimePowerIndex.box N,
      completedAutocorrelationSpectralTransform_weightedPrimeSampling ι f) =
      completedAutocorrelationSpectralTransform_weightedPrimeSamplingWindow N f := by
  unfold completedAutocorrelationSpectralTransform_weightedPrimeSamplingWindow
  exact
    sum_box_completedAutocorrelationSpectralTransform_weightedPrimeSampling_eq_sum_window
      N f

/-- The finite weighted prime-power sampling mass is nonnegative. -/
theorem completedAutocorrelationSpectralTransform_weightedPrimeSamplingWindow_nonnegative
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    0 ≤
      completedAutocorrelationSpectralTransform_weightedPrimeSamplingWindow
        N f := by
  unfold completedAutocorrelationSpectralTransform_weightedPrimeSamplingWindow
  exact Finset.sum_nonneg
    (fun ι _hι =>
      completedAutocorrelationSpectralTransform_weightedPrimeSampling_nonnegative
        ι f)

/-- The finite weighted prime-power sampling mass is the finite sum of the explicit
prime-power weights times the prime-center Plancherel/localization density. -/
theorem completedAutocorrelationSpectralTransform_weightedPrimeSamplingWindow_eq_weight_mul_density_sum
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    completedAutocorrelationSpectralTransform_weightedPrimeSamplingWindow N f =
      ∑ ι in ZetaPrimePowerIndex.window N,
        ZetaPrimePowerIndex.weight ι *
          completedAutocorrelationSpectralTransform_primeCenterPlancherelDensity
            ι f := by
  unfold completedAutocorrelationSpectralTransform_weightedPrimeSamplingWindow
  exact Finset.sum_congr rfl
    (fun ι _hι =>
      completedAutocorrelationSpectralTransform_weightedPrimeSampling_eq_weight_mul_density
        ι f)

/-- The positive seed-face weighted sample-square is the completed spectral-transform
weighted prime sampling family. -/
theorem zetaCompletedPrimePositiveWeightedSampleNormSq_eq_weightedPrimeSampling
    (ι : ZetaPrimePowerIndex) (f : ZetaAdmissibleFunction) :
    zetaCompletedPrimePositiveWeightedSampleNormSq ι f =
      completedAutocorrelationSpectralTransform_weightedPrimeSampling ι f := by
  unfold zetaCompletedPrimePositiveWeightedSampleNormSq
  unfold completedAutocorrelationSpectralTransform_weightedPrimeSampling
  unfold zetaCompletedPrimeHermitianSeedAmplitude
  unfold ZetaPrimePowerIndex.center
  rfl

/-- The opposite weighted prime-center sample-square is the positive sample-square of the
reflected seed. -/
theorem zetaCompletedPrimeOppositeWeightedSampleNormSq_eq_positive_reflect
    (ι : ZetaPrimePowerIndex) (f : ZetaAdmissibleFunction) :
    zetaCompletedPrimeOppositeWeightedSampleNormSq ι f =
      zetaCompletedPrimePositiveWeightedSampleNormSq ι
        (ZetaAdmissibleFunction.reflect f) := by
  have hsample :
      zetaCompletedPrimeHermitianNegativeSeedAmplitude ι.p ι.n f =
        zetaCompletedPrimeHermitianSeedAmplitude ι.p ι.n
          (ZetaAdmissibleFunction.reflect f) := by
    unfold zetaCompletedPrimeHermitianNegativeSeedAmplitude
    unfold zetaCompletedPrimeHermitianSeedAmplitude
    exact
      (zetaCompletedExplicitFormulaPhi_reflect f
        (zetaPrimePacketCenter ι.p ι.n)).symm
  unfold zetaCompletedPrimeOppositeWeightedSampleNormSq
  unfold zetaCompletedPrimePositiveWeightedSampleNormSq
  exact congrArg
    (fun A : ℂ => ZetaPrimePowerIndex.weight ι * ‖A‖ ^ 2)
    hsample

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
    Complex.sum_re
      (fun ι : ZetaPrimePowerIndex =>
        -((ι.weight : ℂ) *
          (zetaCompletedSpectralLaplaceTransform g ι.center +
            star (zetaCompletedSpectralLaplaceTransform g ι.center))))
      (ZetaPrimePowerIndex.window N)

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
  exact (Complex.ofReal_re
    (∑' ι : ZetaPrimePowerIndex,
      -(ι.weight *
        Complex.re
          (zetaCompletedTimeBoundaryValue g ι.center +
            star (zetaCompletedTimeBoundaryValue g ι.center))))).symm

/-- The real spectral prime off-diagonal coordinate in the completed prime-power
explicit-formula distribution. -/
def zetaSpectralPrimeOffDiagonalCoordinate
    (ι : ZetaPrimePowerIndex) (f : ZetaAdmissibleFunction) : ℝ :=
  Complex.re
    (-((ι.weight : ℂ) *
      (zetaCompletedExplicitFormulaPhi (convolutionAutocorrelation f) ι.center +
        star
          (zetaCompletedExplicitFormulaPhi
            (convolutionAutocorrelation f) ι.center))))

/-- The completed spectral prime off-diagonal channel, obtained from the completed
explicit-formula prime-power distribution on the convolution-autocorrelation probe. -/
noncomputable def completedSpectralPrimeOffDiagonalChannel
    (f : ZetaAdmissibleFunction) : ℝ :=
  Complex.re
    (zetaCompletedExplicitFormulaPrimePowerSpectralSampleContribution
      (convolutionAutocorrelation f))

/-- The completed spectral prime channel is the autocorrelation specialization of the
spectral completed prime distribution. -/
theorem completedSpectralPrimeOffDiagonalChannel_eq_spectralDistributionPairing
    (f : ZetaAdmissibleFunction) :
    completedSpectralPrimeOffDiagonalChannel f =
      completedPrimeSpectralDistributionPairing
        (zetaCompletedSpectralLaplaceTransform (convolutionAutocorrelation f)) := by
  unfold completedSpectralPrimeOffDiagonalChannel
  unfold completedPrimeSpectralDistributionPairing
  unfold zetaCompletedExplicitFormulaPrimePowerSpectralSampleContribution
  unfold zetaCompletedSpectralLaplaceTransform
  rfl

/-- The finite physical prime off-diagonal window. -/
def finitePhysicalPrimeOffDiagonalWindow
    (N : ℕ) (f : ZetaAdmissibleFunction) : ℝ :=
  finitePartPrimeOffDiagonalWindow N f

/-- The finite spectral prime off-diagonal window attached to the completed explicit-formula
prime-power distribution. -/
def finiteSpectralPrimeOffDiagonalWindow
    (N : ℕ) (f : ZetaAdmissibleFunction) : ℝ :=
  Complex.re
    (∑ ι in ZetaPrimePowerIndex.window N,
      -((ι.weight : ℂ) *
        (zetaCompletedExplicitFormulaPhi (convolutionAutocorrelation f) ι.center +
          star
            (zetaCompletedExplicitFormulaPhi
              (convolutionAutocorrelation f) ι.center))))

/-- The finite spectral prime window is the finite sum of spectral prime coordinates. -/
theorem finiteSpectralPrimeOffDiagonalWindow_eq_sum_coordinates
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    finiteSpectralPrimeOffDiagonalWindow N f =
      ∑ ι in ZetaPrimePowerIndex.window N,
        zetaSpectralPrimeOffDiagonalCoordinate ι f := by
  unfold finiteSpectralPrimeOffDiagonalWindow
  unfold zetaSpectralPrimeOffDiagonalCoordinate
  exact Complex.sum_re
    (fun ι : ZetaPrimePowerIndex =>
      -((ι.weight : ℂ) *
        (zetaCompletedExplicitFormulaPhi (convolutionAutocorrelation f) ι.center +
          star
            (zetaCompletedExplicitFormulaPhi
              (convolutionAutocorrelation f) ι.center))))
    (ZetaPrimePowerIndex.window N)

/-- Nongenuine indices have zero spectral prime off-diagonal coordinate. -/
theorem zetaSpectralPrimeOffDiagonalCoordinate_eq_zero_of_not_isGenuine
    (ι : ZetaPrimePowerIndex) (f : ZetaAdmissibleFunction)
    (hι : ¬ ZetaPrimePowerIndex.IsGenuine ι) :
    zetaSpectralPrimeOffDiagonalCoordinate ι f = 0 := by
  have hweight : ι.weight = 0 :=
    ZetaPrimePowerIndex.weight_eq_zero_of_not_isGenuine ι hι
  unfold zetaSpectralPrimeOffDiagonalCoordinate
  calc
    Complex.re
        (-((ι.weight : ℂ) *
          (zetaCompletedExplicitFormulaPhi (convolutionAutocorrelation f) ι.center +
            star
              (zetaCompletedExplicitFormulaPhi
                (convolutionAutocorrelation f) ι.center)))) =
        Complex.re
          (-((0 : ℂ) *
            (zetaCompletedExplicitFormulaPhi (convolutionAutocorrelation f) ι.center +
              star
                (zetaCompletedExplicitFormulaPhi
                  (convolutionAutocorrelation f) ι.center)))) := by
      exact congrArg
        (fun x : ℝ =>
          Complex.re
            (-((x : ℂ) *
              (zetaCompletedExplicitFormulaPhi (convolutionAutocorrelation f) ι.center +
                star
                  (zetaCompletedExplicitFormulaPhi
                    (convolutionAutocorrelation f) ι.center)))))
        hweight
    _ = Complex.re (-(0 : ℂ)) := by
      exact congrArg (fun x : ℂ => Complex.re (-x))
        (zero_mul
          (zetaCompletedExplicitFormulaPhi (convolutionAutocorrelation f) ι.center +
            star
              (zetaCompletedExplicitFormulaPhi
                (convolutionAutocorrelation f) ι.center)))
    _ = Complex.re (0 : ℂ) := by
      exact congrArg Complex.re (neg_zero : -(0 : ℂ) = 0)
    _ = 0 := by
      exact Complex.zero_re

/-- The finite physical prime window is the kernel off-diagonal window. -/
theorem finitePhysicalPrimeOffDiagonalWindow_eq_kernelWindow
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    finitePhysicalPrimeOffDiagonalWindow N f =
      primeKernelOffDiagonalBoundaryWindow N f := by
  unfold finitePhysicalPrimeOffDiagonalWindow
  unfold finitePartPrimeOffDiagonalWindow
  exact (primeKernelOffDiagonalBoundaryWindow_eq_physicalPrimeOffDiagonal N f).symm

/-- The finite physical prime windows exhaust the completed physical prime off-diagonal
channel. -/
theorem finitePhysicalPrimeOffDiagonalWindow_tendsto_completedPhysicalPrimeOffDiagonalChannel
    (f : ZetaAdmissibleFunction) :
    Tendsto
      (fun N : ℕ => finitePhysicalPrimeOffDiagonalWindow N f)
      atTop
      (𝓝 (completedPhysicalPrimeOffDiagonalChannel f)) := by
  unfold finitePhysicalPrimeOffDiagonalWindow
  unfold finitePartPrimeOffDiagonalWindow
  unfold completedPhysicalPrimeOffDiagonalChannel
  exact zetaPrimeOffDiagonalChannel_tendsto_completedPrimeOffDiagonalChannel f

/-- Compatibility wrapper for the historical prime-power contribution statement. -/
theorem completedPrimeOffDiagonalChannel_eq_primePowerContribution_re
    (f : ZetaAdmissibleFunction) :
    completedPrimeOffDiagonalChannel f =
      Complex.re
        (zetaCompletedExplicitFormulaPrimePowerContribution
          (convolutionAutocorrelation f)) := by
  have htime :
      completedPhysicalPrimeOffDiagonalChannel f =
        completedPrimeTimeDistributionPairing (convolutionAutocorrelation f) :=
    completedPhysicalPrimeOffDiagonalChannel_eq_timeDistributionPairing f
  have howner :
      completedPrimeTimeDistributionPairing (convolutionAutocorrelation f) =
        Complex.re
          (zetaCompletedExplicitFormulaPrimePowerContribution
            (convolutionAutocorrelation f)) :=
    completedPrimeTimeDistributionPairing_eq_primePowerContribution_re
      (convolutionAutocorrelation f)
  exact htime.trans howner

/-- The completed prime off-diagonal channel is the real part of the explicit-formula prime
boundary channel on the convolution-autocorrelation probe. -/
theorem completedPrimeOffDiagonalChannel_eq_primeBoundaryChannel
    (f : ZetaAdmissibleFunction) :
    completedPrimeOffDiagonalChannel f =
      Complex.re (primeBoundaryChannel (convolutionAutocorrelation f)) := by
  have howner :
      zetaCompletedExplicitFormulaPrimePowerContribution (convolutionAutocorrelation f) =
        zetaCompletedExplicitFormulaPrimeContribution (convolutionAutocorrelation f) :=
    zetaCompletedExplicitFormulaPrimePowerContribution_eq_primeContribution
      (convolutionAutocorrelation f)
  have hphysical :
      completedPrimeOffDiagonalChannel f =
        Complex.re
          (zetaCompletedExplicitFormulaPrimePowerContribution
            (convolutionAutocorrelation f)) := by
    exact completedPrimeOffDiagonalChannel_eq_primePowerContribution_re f
  unfold primeBoundaryChannel
  exact hphysical.trans (congrArg Complex.re howner)

/-- The completed time-side prime distribution is the completed off-diagonal channel. -/
theorem completedPrimeTimeDistributionPairing_eq_completedPrimeOffDiagonalChannel
    (f : ZetaAdmissibleFunction) :
    completedPrimeTimeDistributionPairing (convolutionAutocorrelation f) =
      completedPrimeOffDiagonalChannel f := by
  have hphysical :
      completedPhysicalPrimeOffDiagonalChannel f =
        completedPrimeTimeDistributionPairing (convolutionAutocorrelation f) :=
    completedPhysicalPrimeOffDiagonalChannel_eq_timeDistributionPairing f
  unfold completedPhysicalPrimeOffDiagonalChannel at hphysical
  exact hphysical.symm

/-- Concrete owner data for completed finite-window prime distribution reconstruction.

The datum records the common finite reconstruction stream, its time/log and
contour-realized presentations, and convergence of both presentations to their completed
pairings.  It is deliberately lower than tomography: scheduled contour machinery may build
this object downstream, while this distribution file only consumes the explicit
finite-window reconstruction data and never identifies raw time boundary values with
spectral Laplace samples coordinatewise. -/
structure CompletedFiniteWindowPrimeDistributionReconstruction
    (f : ZetaAdmissibleFunction) where
  finiteWindow : ℕ → ℝ
  finiteWindow_eq_timeWindow :
    ∀ N : ℕ,
      finiteWindow N =
        finitePrimeTimeDistributionWindow N (convolutionAutocorrelation f)
  finiteWindow_eq_contourWindow :
    ∀ N : ℕ,
      finiteWindow N =
        finitePrimeContourRealizedTimeDistributionWindow N
          (convolutionAutocorrelation f)
  timeWindow_tendsto :
    Tendsto
      (fun N : ℕ =>
        finitePrimeTimeDistributionWindow N (convolutionAutocorrelation f))
      atTop
      (𝓝 (completedPrimeTimeDistributionPairing
        (convolutionAutocorrelation f)))
  contourWindow_tendsto :
    Tendsto
      (fun N : ℕ =>
        finitePrimeContourRealizedTimeDistributionWindow N
          (convolutionAutocorrelation f))
      atTop
      (𝓝 (completedPrimeContourRealizedTimeDistributionPairing
        (convolutionAutocorrelation f)))

/-- The reconstructed finite-window stream tends to the completed time/log pairing. -/
theorem CompletedFiniteWindowPrimeDistributionReconstruction.finiteWindow_tendsto_timePairing
    (f : ZetaAdmissibleFunction)
    (D : CompletedFiniteWindowPrimeDistributionReconstruction f) :
    Tendsto D.finiteWindow atTop
      (𝓝 (completedPrimeTimeDistributionPairing
        (convolutionAutocorrelation f))) := by
  have hfun :
      D.finiteWindow =
        fun N : ℕ =>
          finitePrimeTimeDistributionWindow N (convolutionAutocorrelation f) := by
    funext N
    exact D.finiteWindow_eq_timeWindow N
  exact Eq.subst
    (motive := fun u : ℕ → ℝ =>
      Tendsto u atTop
        (𝓝 (completedPrimeTimeDistributionPairing
          (convolutionAutocorrelation f))))
    hfun.symm
    D.timeWindow_tendsto

/-- The reconstructed finite-window stream tends to the completed contour-realized
pairing. -/
theorem CompletedFiniteWindowPrimeDistributionReconstruction.finiteWindow_tendsto_contourPairing
    (f : ZetaAdmissibleFunction)
    (D : CompletedFiniteWindowPrimeDistributionReconstruction f) :
    Tendsto D.finiteWindow atTop
      (𝓝 (completedPrimeContourRealizedTimeDistributionPairing
        (convolutionAutocorrelation f))) := by
  have hfun :
      D.finiteWindow =
        fun N : ℕ =>
          finitePrimeContourRealizedTimeDistributionWindow N
            (convolutionAutocorrelation f) := by
    funext N
    exact D.finiteWindow_eq_contourWindow N
  exact Eq.subst
    (motive := fun u : ℕ → ℝ =>
      Tendsto u atTop
        (𝓝 (completedPrimeContourRealizedTimeDistributionPairing
          (convolutionAutocorrelation f))))
    hfun.symm
    D.contourWindow_tendsto

/-- Completed finite-window prime transport identifies the time/log pairing with the
contour-realized spectral pairing.

This is the owner reconstruction theorem for the completed prime distribution: finite
prime windows are transported through the completed contour realization, the omitted tails
converge, and the resulting completed contour pairing is the same scalar as the completed
time/log distribution pairing.

The proof is not coordinatewise: it must pass through the completed distribution and
contour-realization construction, rather than identifying raw time boundary values with
Laplace samples. -/
theorem completedPrimeDistributionTransport_finiteWindow_contourReconstruction
    (f : ZetaAdmissibleFunction)
    (D : CompletedFiniteWindowPrimeDistributionReconstruction f) :
    completedPrimeTimeDistributionPairing (convolutionAutocorrelation f) =
      completedPrimeContourRealizedTimeDistributionPairing
        (convolutionAutocorrelation f) := by
  have htime :
      Tendsto D.finiteWindow atTop
        (𝓝 (completedPrimeTimeDistributionPairing
          (convolutionAutocorrelation f))) :=
    CompletedFiniteWindowPrimeDistributionReconstruction.finiteWindow_tendsto_timePairing
      f D
  have hcontour :
      Tendsto D.finiteWindow atTop
        (𝓝 (completedPrimeContourRealizedTimeDistributionPairing
          (convolutionAutocorrelation f))) :=
    CompletedFiniteWindowPrimeDistributionReconstruction.finiteWindow_tendsto_contourPairing
      f D
  exact tendsto_nhds_unique htime hcontour

/-- Completed finite-window prime transport identifies the time/log pairing with the
contour-realized spectral pairing.

This is the genuine transport statement behind the real-part presentation theorem below:
the finite-window prime distribution is reconstructed through the completed contour
realization before passing to the completed limit.  It is not a pointwise identification of
raw time boundary values with spectral samples. -/
theorem completedPrimeDistributionTransport_timePairing_eq_contourRealizedPairing_ownerFiniteWindowTransport
    (f : ZetaAdmissibleFunction)
    (D : CompletedFiniteWindowPrimeDistributionReconstruction f) :
    completedPrimeTimeDistributionPairing (convolutionAutocorrelation f) =
      completedPrimeContourRealizedTimeDistributionPairing
        (convolutionAutocorrelation f) := by
  exact completedPrimeDistributionTransport_finiteWindow_contourReconstruction f D

/-- Completed prime-power transport from the time/log presentation to the spectral-sample
presentation on an autocorrelation probe.

This is the irreducible comparison content behind the prime transport bridge: the completed
time-side prime-power contribution and the completed contour/spectral prime-power
contribution are two presentations of the same completed finite-window prime transport. -/
theorem completedPrimeOffDiagonalChannel_eq_completedSpectralPrimeOffDiagonalChannel_ownerDistributionTransport_core
    (f : ZetaAdmissibleFunction)
    (D : CompletedFiniteWindowPrimeDistributionReconstruction f) :
    completedPrimeOffDiagonalChannel f =
      completedSpectralPrimeOffDiagonalChannel f := by
  have htime :
      completedPrimeOffDiagonalChannel f =
        completedPrimeTimeDistributionPairing (convolutionAutocorrelation f) :=
    completedPrimeTimeDistributionPairing_eq_completedPrimeOffDiagonalChannel f
  have htransport :
      completedPrimeTimeDistributionPairing (convolutionAutocorrelation f) =
        completedPrimeContourRealizedTimeDistributionPairing
          (convolutionAutocorrelation f) :=
    completedPrimeDistributionTransport_timePairing_eq_contourRealizedPairing_ownerFiniteWindowTransport
      f D
  have hcontour :
      completedPrimeContourRealizedTimeDistributionPairing
          (convolutionAutocorrelation f) =
        completedSpectralPrimeOffDiagonalChannel f := by
    have hrealized :
        completedPrimeContourRealizedTimeDistributionPairing
            (convolutionAutocorrelation f) =
          completedPrimeSpectralDistributionPairing
            (zetaCompletedSpectralLaplaceTransform
              (convolutionAutocorrelation f)) := by
      rfl
    have hspectral :
        completedSpectralPrimeOffDiagonalChannel f =
          completedPrimeSpectralDistributionPairing
            (zetaCompletedSpectralLaplaceTransform
              (convolutionAutocorrelation f)) :=
      completedSpectralPrimeOffDiagonalChannel_eq_spectralDistributionPairing
        f
    exact hrealized.trans hspectral.symm
  exact htime.trans (htransport.trans hcontour)

/-- Completed prime-power transport from the time/log presentation to the spectral-sample
presentation on an autocorrelation probe.

This is the irreducible comparison content behind the prime transport bridge: the completed
time-side prime-power contribution and the completed contour/spectral prime-power
contribution are two presentations of the same completed finite-window prime transport. -/
theorem zetaCompletedExplicitFormulaPrimePowerContribution_re_eq_spectralSampleContribution_re_ownerDistributionTransport
    (f : ZetaAdmissibleFunction)
    (D : CompletedFiniteWindowPrimeDistributionReconstruction f) :
    Complex.re
        (zetaCompletedExplicitFormulaPrimePowerContribution
          (convolutionAutocorrelation f)) =
      Complex.re
        (zetaCompletedExplicitFormulaPrimePowerSpectralSampleContribution
          (convolutionAutocorrelation f)) := by
  have hchannel :
      completedPrimeOffDiagonalChannel f =
        completedSpectralPrimeOffDiagonalChannel f :=
    completedPrimeOffDiagonalChannel_eq_completedSpectralPrimeOffDiagonalChannel_ownerDistributionTransport_core
      f D
  exact hchannel

/-- Completed prime distribution transport from the physical/time presentation to the
spectral contour presentation.

This is the owner bridge comparing the completed time/log-side prime channel with the
completed spectral/Laplace-side prime channel.  It is not a pointwise identification of
time samples with Laplace samples; it is the completed finite-window transport statement. -/
theorem completedPrimeOffDiagonalChannel_eq_completedSpectralPrimeOffDiagonalChannel_ownerDistributionTransport
    (f : ZetaAdmissibleFunction)
    (D : CompletedFiniteWindowPrimeDistributionReconstruction f) :
    completedPrimeOffDiagonalChannel f =
      completedSpectralPrimeOffDiagonalChannel f := by
  exact completedPrimeOffDiagonalChannel_eq_completedSpectralPrimeOffDiagonalChannel_ownerDistributionTransport_core
    f D

/-- Completed prime finite-window normalization reaches the two-face/GNS boundary scalar.

This is the owner bridge from the physical/time-side completed prime finite-part channel
to the completed two-face/GNS boundary coefficient.  It is the completed form of the
finite defect-square expansion plus diagonal-debt absorption. -/
theorem completedPrimeOffDiagonalChannel_eq_completedTwoFaceGNSBoundaryCoefficient_re_ownerDistributionTransport
    (f : ZetaAdmissibleFunction)
    (D : CompletedFiniteWindowPrimeDistributionReconstruction f) :
    completedPrimeOffDiagonalChannel f =
      Complex.re (zetaCompletedPrimeTwoFaceGNSBoundaryCoefficient f) := by
  have hspectral :
      completedPrimeOffDiagonalChannel f =
        completedSpectralPrimeOffDiagonalChannel f :=
    completedPrimeOffDiagonalChannel_eq_completedSpectralPrimeOffDiagonalChannel_ownerDistributionTransport
      f D
  unfold completedSpectralPrimeOffDiagonalChannel at hspectral
  unfold zetaCompletedPrimeTwoFaceGNSBoundaryCoefficient
  exact hspectral

/-- The prime boundary channel of the convolution pair is the raw time-side prime
distribution. -/
theorem primeBoundaryChannel_convolutionPair_re_eq_timeDistributionPairing
    (f : ZetaAdmissibleFunction) :
    Complex.re (primeBoundaryChannel (convolutionPair f f)) =
      completedPrimeTimeDistributionPairing (convolutionAutocorrelation f) := by
  have hpair :
      convolutionPair f f = convolutionAutocorrelation f :=
    convolutionPair_self f
  have htime :
      completedPrimeTimeDistributionPairing (convolutionAutocorrelation f) =
        Complex.re
          (zetaCompletedExplicitFormulaPrimePowerContribution
            (convolutionAutocorrelation f)) :=
    completedPrimeTimeDistributionPairing_eq_primePowerContribution_re
      (convolutionAutocorrelation f)
  have hprime :
      zetaCompletedExplicitFormulaPrimePowerContribution
          (convolutionAutocorrelation f) =
        primeBoundaryChannel (convolutionAutocorrelation f) := by
    unfold primeBoundaryChannel
    exact zetaCompletedExplicitFormulaPrimePowerContribution_eq_primeContribution
      (convolutionAutocorrelation f)
  have hchannel :
      Complex.re (primeBoundaryChannel (convolutionPair f f)) =
        Complex.re (primeBoundaryChannel (convolutionAutocorrelation f)) :=
    congrArg
      (fun g : ZetaAdmissibleFunction => Complex.re (primeBoundaryChannel g))
      hpair
  exact hchannel.trans ((congrArg Complex.re hprime).symm.trans htime.symm)

/-- The completed spectral prime channel is the real part of the contour-side spectral-sample
prime-power presentation. -/
theorem completedSpectralPrimeOffDiagonalChannel_eq_spectralSampleContribution_re
    (f : ZetaAdmissibleFunction) :
    completedSpectralPrimeOffDiagonalChannel f =
      Complex.re
        (zetaCompletedExplicitFormulaPrimePowerSpectralSampleContribution
          (convolutionAutocorrelation f)) := by
  rfl

/-- The completed spectral prime channel is the real part of the completed two-face boundary
coefficient.  This is the algebraic half of prime tomography after the contour-side spectral
sample has been formed. -/
theorem completedSpectralPrimeOffDiagonalChannel_eq_completedTwoFaceBoundaryCoefficient_re
    (f : ZetaAdmissibleFunction) :
    completedSpectralPrimeOffDiagonalChannel f =
      Complex.re (zetaCompletedPrimeTwoFaceGNSBoundaryCoefficient f) := by
  unfold completedSpectralPrimeOffDiagonalChannel
  unfold zetaCompletedExplicitFormulaPrimePowerSpectralSampleContribution
  have hsum :
      (∑' ι : ZetaPrimePowerIndex,
          -((ι.weight : ℂ) *
            (zetaCompletedExplicitFormulaPhi
                (convolutionAutocorrelation f) ι.center +
              star
                (zetaCompletedExplicitFormulaPhi
                  (convolutionAutocorrelation f) ι.center)))) =
        zetaCompletedPrimeTwoFaceGNSBoundaryCoefficient f := by
    calc
      (∑' ι : ZetaPrimePowerIndex,
          -((ι.weight : ℂ) *
            (zetaCompletedExplicitFormulaPhi
                (convolutionAutocorrelation f) ι.center +
              star
                (zetaCompletedExplicitFormulaPhi
                  (convolutionAutocorrelation f) ι.center)))) =
          ∑' ι : ZetaPrimePowerIndex,
            -zetaCompletedPrimeTwoFaceGNSSymmetrizedCoordinate ι f := by
        exact tsum_congr
          (fun ι : ZetaPrimePowerIndex =>
            zetaCompletedPrimeSpectralSampleCoordinate_eq_neg_twoFaceBoundaryCoordinate
              ι f)
      _ = zetaCompletedPrimeTwoFaceGNSBoundaryCoefficient f := by
        exact zetaCompletedPrimeTwoFaceGNSBoundaryCoordinate_tsum_eq_boundaryCoefficient f
  exact congrArg Complex.re hsum

/-- A finitely supported real prime-power family is bounded by a rectangular-height
polynomial majorant.

This is the finite-support owner lemma behind raw time-side prime-coordinate
localization: on the finite support choose one constant dominating the finitely many
ratios by the strictly positive height decay; off the support the family vanishes. -/
theorem exists_rawHeightPolynomialBound_of_finsetSupport
    (u : ZetaPrimePowerIndex → ℝ)
    (s : Finset ZetaPrimePowerIndex)
    (hsupport : ∀ ι : ZetaPrimePowerIndex, ι ∉ s → u ι = 0) :
    ∃ C : ℝ, ∃ k : ℕ,
      0 < C ∧
      ∀ ι : ZetaPrimePowerIndex,
        ‖u ι‖ ≤ C * ZetaPrimePowerIndex.polynomialHeightDecay k ι := by
  let d : ZetaPrimePowerIndex → ℝ :=
    fun ι => ZetaPrimePowerIndex.polynomialHeightDecay 0 ι
  let q : ZetaPrimePowerIndex → ℝ :=
    fun ι => ‖u ι‖ / d ι
  let C : ℝ := (∑ ι in s, q ι) + 1
  have hq_nonnegative :
      ∀ ι : ZetaPrimePowerIndex, 0 ≤ q ι := by
    intro ι
    exact div_nonneg
      (norm_nonneg (u ι))
      (le_of_lt (ZetaPrimePowerIndex.polynomialHeightDecay_pos 0 ι))
  have hsum_nonnegative : 0 ≤ ∑ ι in s, q ι := by
    exact Finset.sum_nonneg
      (fun ι _hι => hq_nonnegative ι)
  have hC_positive : 0 < C := by
    exact add_pos_of_nonneg_of_pos hsum_nonnegative zero_lt_one
  refine ⟨C, 0, hC_positive, ?_⟩
  intro ι
  have hd_positive : 0 < d ι :=
    ZetaPrimePowerIndex.polynomialHeightDecay_pos 0 ι
  by_cases hι : ι ∈ s
  · have hq_le_sum : q ι ≤ ∑ η in s, q η := by
      exact Finset.single_le_sum
        (fun η _hη => hq_nonnegative η)
        hι
    have hq_le_C : q ι ≤ C := by
      exact le_trans hq_le_sum
        (le_add_of_nonneg_right zero_le_one)
    have hscaled : q ι * d ι ≤ C * d ι := by
      exact mul_le_mul_of_nonneg_right hq_le_C (le_of_lt hd_positive)
    have hrecover : q ι * d ι = ‖u ι‖ := by
      exact div_mul_cancel₀ (‖u ι‖) (ne_of_gt hd_positive)
    calc
      ‖u ι‖ = q ι * d ι := by
        exact hrecover.symm
      _ ≤ C * d ι := by
        exact hscaled
  · have hu_zero : u ι = 0 :=
      hsupport ι hι
    have hnorm_zero : ‖u ι‖ = 0 :=
      congrArg norm hu_zero
    have hright_nonnegative : 0 ≤ C * d ι :=
      mul_nonneg (le_of_lt hC_positive) (le_of_lt hd_positive)
    calc
      ‖u ι‖ = 0 := by
        exact hnorm_zero
      _ ≤ C * d ι := by
        exact hright_nonnegative

/-- Raw height-polynomial localization for the time-side prime distribution coordinate. -/
theorem exists_completedPrimeTimeDistributionCoordinate_rawHeightBound
    (f : ZetaAdmissibleFunction) :
    ∃ C : ℝ, ∃ k : ℕ,
      0 < C ∧
      ∀ ι : ZetaPrimePowerIndex,
        ‖completedPrimeTimeDistributionCoordinate
            ι (convolutionAutocorrelation f)‖ ≤
          C * ZetaPrimePowerIndex.polynomialHeightDecay k ι := by
  exact
    match exists_convolutionAutocorrelationKernelSupportUpperBound f with
    | ⟨B, hB⟩ =>
      exists_rawHeightPolynomialBound_of_finsetSupport
        (fun ι : ZetaPrimePowerIndex =>
          completedPrimeTimeDistributionCoordinate
            ι (convolutionAutocorrelation f))
        (zetaPrimeOffDiagonalSupportFinsetOfBound f B)
        (fun ι hι =>
          (completedPrimeTimeDistributionCoordinate_convolutionAutocorrelation_eq_physical
            ι f).trans
            (zetaPrimeOffDiagonalCoordinate_eq_zero_of_not_mem_supportFinsetOfBound
              ι f hB hι))

end ZetaAdmissibleFunction

end

end LFunctions
end Boundary
