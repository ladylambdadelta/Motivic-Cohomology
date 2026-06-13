import Boundary.LFunctions.ZetaCompletedSquareLedger
import Boundary.LFunctions.ZetaTransformCalculusBase
import Boundary.LFunctions.ZetaTransformCalculusWeighted
import Boundary.LFunctions.ZetaPacketComparison
import Boundary.LFunctions.ZetaHermitianPacket
import Boundary.LFunctions.ZetaExplicitFormulaComplexAnalysis

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
