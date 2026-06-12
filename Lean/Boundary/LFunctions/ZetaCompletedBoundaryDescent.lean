import Boundary.LFunctions.ZetaCompletedSquareLedger
import Boundary.LFunctions.ZetaTransformCalculusBase
import Boundary.LFunctions.ZetaPacketComparison
import Boundary.LFunctions.ZetaHermitianPacket

/-!
# Boundary completed-channel descent

This file owns the concrete descent and compatibility statements for the
completed explicit-formula boundary channel.  It deliberately uses named
channel definitions and named theorems rather than an abstract prerequisite
record.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open Filter
open scoped Topology

namespace ZetaAdmissibleFunction

/-- The completed explicit-formula boundary channel. -/
def completedBoundaryChannel (g : ZetaAdmissibleFunction) : ℂ :=
  zetaCompletedExplicitFormulaBoundarySumCore g

/-- The prime channel of the completed boundary functional. -/
def primeBoundaryChannel (g : ZetaAdmissibleFunction) : ℂ :=
  zetaCompletedExplicitFormulaPrimeContribution g

/-- The opposite prime face of the completed boundary functional.  This is the negative
prime-power face paired with the positive prime channel by dagger. -/
def oppositePrimeBoundaryChannel (g : ZetaAdmissibleFunction) : ℂ :=
  ∑ ℓ in zetaCompletedExplicitFormulaPrimeSupport,
    -((zetaCompletedExplicitFormulaPrimeWeight ℓ.1 ℓ.2 : ℂ) *
      zetaCompletedExplicitFormulaPhi g (-(zetaPrimePacketCenter ℓ.1 ℓ.2 : ℂ)))

/-- The archimedean channel of the completed boundary functional. -/
def archimedeanBoundaryChannel (g : ZetaAdmissibleFunction) : ℂ :=
  zetaCompletedExplicitFormulaArchimedeanContribution g

/-- The pole channel in the current centered completed-zeta normalization. -/
def poleBoundaryChannel (g : ZetaAdmissibleFunction) : ℂ :=
  zetaCompletedExplicitFormulaCorrectionContribution g

/-- The residual completion channel after the explicit archimedean and pole channels have been
separated.  In the current normalization this channel is zero; if the gamma normalization is
split further, this is the owner slot to refine. -/
def completionBoundaryChannel (_g : ZetaAdmissibleFunction) : ℂ :=
  0

/-- The opposite completed boundary channel.  The prime face is reflected to the negative
prime-power face; the self-paired archimedean and correction faces remain at the basepoint. -/
def oppositeBoundaryChannel (g : ZetaAdmissibleFunction) : ℂ :=
  oppositePrimeBoundaryChannel g +
    archimedeanBoundaryChannel g +
    poleBoundaryChannel g +
    completionBoundaryChannel g

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

/-- The local channel decomposition of the completed boundary functional. -/
theorem completedBoundaryChannel_eq_prime_add_archimedean_add_pole_add_completion
    (g : ZetaAdmissibleFunction) :
    completedBoundaryChannel g =
      primeBoundaryChannel g +
        archimedeanBoundaryChannel g +
        poleBoundaryChannel g +
        completionBoundaryChannel g := by
  unfold completedBoundaryChannel
  unfold primeBoundaryChannel
  unfold archimedeanBoundaryChannel
  unfold poleBoundaryChannel
  unfold completionBoundaryChannel
  calc
    zetaCompletedExplicitFormulaBoundarySumCore g =
        zetaCompletedExplicitFormulaPrimeContribution g +
          zetaCompletedExplicitFormulaArchimedeanContribution g +
          zetaCompletedExplicitFormulaCorrectionContribution g :=
      zetaCompletedExplicitFormulaBoundarySumCore_eq g
    _ =
        zetaCompletedExplicitFormulaPrimeContribution g +
          zetaCompletedExplicitFormulaArchimedeanContribution g +
          zetaCompletedExplicitFormulaCorrectionContribution g + 0 := by
      exact (add_zero _).symm

/-- The Hermitian kernel assembled from the completed boundary channels on the convolution
pairing algebra. -/
def completedHermitianKernel
    (f h : ZetaAdmissibleFunction) : ℂ :=
  primeBoundaryChannel (convolutionPair f h) +
    archimedeanBoundaryChannel (convolutionPair f h) +
    poleBoundaryChannel (convolutionPair f h) +
    completionBoundaryChannel (convolutionPair f h)

/-- The completed boundary channel of a convolution pair is the completed Hermitian kernel. -/
theorem completedBoundaryChannel_convolutionPair_eq_kernel
    (f h : ZetaAdmissibleFunction) :
    completedBoundaryChannel (convolutionPair f h) =
      completedHermitianKernel f h := by
  exact completedBoundaryChannel_eq_prime_add_archimedean_add_pole_add_completion
    (convolutionPair f h)

/-- The diagonal convolution-pair transport specializes to the completed autocorrelation
boundary channel. -/
theorem completedBoundaryChannel_convolutionAutocorrelation_eq_kernel_diagonal
    (f : ZetaAdmissibleFunction) :
    completedBoundaryChannel (convolutionAutocorrelation f) =
      completedHermitianKernel f f := by
  exact
    Eq.subst
      (motive := fun g : ZetaAdmissibleFunction =>
        completedBoundaryChannel g = completedHermitianKernel f f)
      (convolutionPair_self f)
      (completedBoundaryChannel_convolutionPair_eq_kernel f f)

/-- Transform compatibility for two-variable convolution-pair kernels. -/
theorem zetaLaplaceTransform_convolutionPair
    (f h : ZetaAdmissibleFunction) (z : ℂ) :
    Boundary.zetaLaplaceTransform (convolutionPair f h).toZetaTestFunction' z =
      Boundary.zetaLaplaceTransform f.toZetaTestFunction' z *
        star (Boundary.zetaLaplaceTransform h.toZetaTestFunction' (-star z)) := by
  exact Boundary.zetaLaplaceTransform_convolutionPair f h z

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
      (zetaLaplaceTransform_convolutionPair
        f h (zetaPrimePacketCenter ℓ.1 ℓ.2))
  have harch :
      (2 : ℂ) * zetaCompletedExplicitFormulaPhi (convolutionPair f h) 0 =
        (2 : ℂ) *
          (zetaCompletedExplicitFormulaPhi f 0 *
            star (zetaCompletedExplicitFormulaPhi h (-star (0 : ℂ)))) := by
    unfold zetaCompletedExplicitFormulaPhi
    unfold zetaAutocorrelationSpectralTransform
    exact congrArg (fun z : ℂ => (2 : ℂ) * z)
      (zetaLaplaceTransform_convolutionPair f h 0)
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
    (zetaLaplaceTransform_convolutionPair f h ι.center)

/-- The finite completed physical boundary channel attached to the `N`th prime-power window. -/
def completedBoundaryWindow
    (N : ℕ) (f : ZetaAdmissibleFunction) : ℝ :=
  zetaCompletedPhysicalAutocorrelationBoundaryChannel N f

/-- The physical prime off-diagonal boundary window evaluates the convolution autocorrelation
kernel at prime-power centers.  This is distinct from the Laplace-transform spectral window. -/
def primeKernelOffDiagonalBoundaryWindow
    (N : ℕ) (f : ZetaAdmissibleFunction) : ℝ :=
  ∑ ι in ZetaPrimePowerIndex.window N,
    - (2 * ι.weight * Complex.re (convolutionAutocorrelationKernel f ι.center))

/-- The kernel-level prime off-diagonal window is the physical prime off-diagonal channel. -/
theorem primeKernelOffDiagonalBoundaryWindow_eq_physicalPrimeOffDiagonal
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    primeKernelOffDiagonalBoundaryWindow N f =
      zetaPrimeOffDiagonalChannel N f := by
  unfold primeKernelOffDiagonalBoundaryWindow
  unfold zetaPrimeOffDiagonalChannel
  refine Finset.sum_congr rfl ?_
  intro ι hι
  unfold zetaPrimeOffDiagonalCoordinate
  have hkernel :
      convolutionAutocorrelationKernel f ι.center =
        zetaSeedInner (zetaTranslate ι.center f) f :=
    convolutionAutocorrelationKernel_eq_translateInner f ι.center
  exact congrArg
    (fun x : ℝ => - (2 * ι.weight * x))
    (congrArg Complex.re hkernel)

/-- The completed physical boundary window is the kernel off-diagonal window plus the
archimedean/correction square channel. -/
theorem completedBoundaryWindow_eq_primeKernelOffDiagonal_add_archimedeanCorrection
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    completedBoundaryWindow N f =
      primeKernelOffDiagonalBoundaryWindow N f +
        zetaArchimedeanCorrectionAutocorrelationChannel f := by
  have hprime :=
    primeKernelOffDiagonalBoundaryWindow_eq_physicalPrimeOffDiagonal N f
  unfold completedBoundaryWindow
  unfold zetaCompletedPhysicalAutocorrelationBoundaryChannel
  calc
    zetaPrimeOffDiagonalChannel N f +
        zetaArchimedeanCorrectionAutocorrelationChannel f =
        zetaPrimeOffDiagonalChannel N f +
          zetaArchimedeanCorrectionAutocorrelationChannel f := by
      rfl
    _ =
        primeKernelOffDiagonalBoundaryWindow N f +
          zetaArchimedeanCorrectionAutocorrelationChannel f := by
      exact congrArg
        (fun x : ℝ => x + zetaArchimedeanCorrectionAutocorrelationChannel f)
        hprime.symm

/-- The completed physical boundary window unfolds to the prime off-diagonal window plus the
archimedean/correction channel. -/
theorem completedBoundaryWindow_eq_primeOffDiagonal_add_archimedeanCorrection
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    completedBoundaryWindow N f =
      zetaPrimeOffDiagonalChannel N f +
        zetaArchimedeanCorrectionAutocorrelationChannel f := by
  rfl

/-- The smaller prime-power window embeds into the larger one compatibly with the completed
physical boundary presentation. -/
theorem completedBoundaryWindow_mono_compat
    {N M : ℕ} (hNM : N ≤ M) (f : ZetaAdmissibleFunction) :
    zetaPrimeOffDiagonalChannel N f =
      ∑ ι in (ZetaPrimePowerIndex.window M).filter
          (fun ι => ι ∈ ZetaPrimePowerIndex.window N),
        zetaPrimeOffDiagonalCoordinate ι f := by
  unfold zetaPrimeOffDiagonalChannel
  have hwindow :
      (ZetaPrimePowerIndex.window M).filter
          (fun ι => ι ∈ ZetaPrimePowerIndex.window N) =
        ZetaPrimePowerIndex.window N := by
    ext ι
    constructor
    · intro hι
      exact (Finset.mem_filter.mp hι).2
    · intro hι
      exact Finset.mem_filter.mpr
        ⟨ZetaPrimePowerIndex.window_mono hNM hι, hι⟩
  exact congrArg
    (fun s : Finset ZetaPrimePowerIndex =>
      ∑ ι in s, zetaPrimeOffDiagonalCoordinate ι f)
    hwindow.symm

/-- The debt-corrected finite completed boundary window.  This is the finite approximant in the
completed normalization; the raw finite physical window alone is not the approximating object. -/
def completedCorrectedBoundaryWindow
    (N : ℕ) (f : ZetaAdmissibleFunction) : ℝ :=
  completedBoundaryWindow N f + zetaPrimeDiagonalDebt N f

/-- The finite positive square-energy window after adding diagonal debt.  This object is used
for positivity; it is not itself the renormalized finite-part distribution unless the diagonal
debt has also been cancelled by a completed normalization channel. -/
def finitePositiveSquareEnergyWindow
    (N : ℕ) (f : ZetaAdmissibleFunction) : ℝ :=
  zetaCompletedPhysicalAutocorrelationSquareEnergy N f

/-- The prime off-diagonal finite-part window.  This is the prime channel after diagonal debt
has been removed from the finite-part distribution. -/
def finitePartPrimeOffDiagonalWindow
    (N : ℕ) (f : ZetaAdmissibleFunction) : ℝ :=
  zetaPrimeOffDiagonalChannel N f

/-- The finite diagonal-debt absorption channel. This is deliberately separate from the
archimedean and correction channels: it is the normalization channel that cancels the diagonal
part of the prime defect square after the positive prime kernel has been expanded. -/
def finitePartDebtAbsorptionWindow
    (N : ℕ) (f : ZetaAdmissibleFunction) : ℝ :=
  - zetaPrimeDiagonalDebt N f

/-- Backwards-compatible name for the finite diagonal-debt absorption channel. -/
def finitePartDiagonalDebtCancellationWindow
    (N : ℕ) (f : ZetaAdmissibleFunction) : ℝ :=
  finitePartDebtAbsorptionWindow N f

/-- The archimedean/correction finite channel.  Diagonal-debt absorption is not hidden here;
it is a separate normalization channel. -/
def finitePartArchimedeanCorrectionWindow
    (_N : ℕ) (f : ZetaAdmissibleFunction) : ℝ :=
  zetaArchimedeanCorrectionAutocorrelationChannel f

/-- The renormalized finite-part completed boundary window.  This is the object whose limit is
the completed boundary channel; the positive square-energy window is related to it only after
adding the diagonal debt. -/
def finitePartBoundaryWindow
    (N : ℕ) (f : ZetaAdmissibleFunction) : ℝ :=
  finitePartPrimeOffDiagonalWindow N f +
    zetaPrimeDiagonalDebt N f +
    finitePartDebtAbsorptionWindow N f +
    finitePartArchimedeanCorrectionWindow N f

/-- The positive square-energy window after applying the finite diagonal-debt absorption
normalization.  This is the bridge object between finite positivity and the finite-part
completed boundary window. -/
def finitePositiveRenormalizedBoundaryWindow
    (N : ℕ) (f : ZetaAdmissibleFunction) : ℝ :=
  completedCorrectedBoundaryWindow N f +
    finitePartDebtAbsorptionWindow N f

/-- The finite boundary weight packet for one cutoff.  It keeps the positive square object,
the prime cross term, the diagonal debt, its absorption channel, and the archimedean/correction
term as separate coordinates. -/
structure FiniteBoundaryWeightObject where
  positiveSquare : ℝ
  primeCross : ℝ
  diagonalDebt : ℝ
  debtAbsorption : ℝ
  archCorrection : ℝ

/-- The concrete finite boundary weight packet attached to a cutoff and admissible seed. -/
def finiteBoundaryWeightObject
    (N : ℕ) (f : ZetaAdmissibleFunction) : FiniteBoundaryWeightObject :=
  { positiveSquare := finitePositiveSquareEnergyWindow N f
    primeCross := finitePartPrimeOffDiagonalWindow N f
    diagonalDebt := zetaPrimeDiagonalDebt N f
    debtAbsorption := finitePartDebtAbsorptionWindow N f
    archCorrection := finitePartArchimedeanCorrectionWindow N f }

namespace FiniteBoundaryWeightObject

/-- The finite square representative scalar. -/
def squareRepresentative (x : FiniteBoundaryWeightObject) : ℝ :=
  x.positiveSquare

/-- The finite-part representative scalar after triangular debt absorption. -/
def finitePartRepresentative (x : FiniteBoundaryWeightObject) : ℝ :=
  x.primeCross + x.diagonalDebt + x.debtAbsorption + x.archCorrection

/-- The absorbed square representative scalar. -/
def absorbedSquareRepresentative (x : FiniteBoundaryWeightObject) : ℝ :=
  x.positiveSquare + x.debtAbsorption

/-- The finite diagonal-plus-absorption lower-weight scalar component. -/
def lowerWeightExactRepresentative (x : FiniteBoundaryWeightObject) : ℝ :=
  x.diagonalDebt + x.debtAbsorption

end FiniteBoundaryWeightObject

/-- A concrete lower-weight absorption certificate for a finite boundary packet.  It records
only proved scalar identities: diagonal debt cancels with the absorption channel, and the
absorbed square representative is the finite-part representative. -/
structure FiniteBoundaryLowerWeightAbsorptionCert
    (x : FiniteBoundaryWeightObject) where
  debt_absorption_cancel :
    x.diagonalDebt + x.debtAbsorption = 0
  absorbed_square_eq_finitePart :
    FiniteBoundaryWeightObject.absorbedSquareRepresentative x =
      FiniteBoundaryWeightObject.finitePartRepresentative x

namespace FiniteBoundaryLowerWeightAbsorptionCert

/-- A finite lower-weight absorption certificate says that the lower-weight representative is
exact. -/
theorem lowerWeightExactRepresentative_eq_zero
    {x : FiniteBoundaryWeightObject}
    (h : FiniteBoundaryLowerWeightAbsorptionCert x) :
    FiniteBoundaryWeightObject.lowerWeightExactRepresentative x = 0 := by
  unfold FiniteBoundaryWeightObject.lowerWeightExactRepresentative
  exact h.debt_absorption_cancel

/-- A finite lower-weight absorption certificate transports the positive square representative
to the finite-part representative. -/
theorem weightTriangularTransport
    {x : FiniteBoundaryWeightObject}
    (h : FiniteBoundaryLowerWeightAbsorptionCert x) :
    FiniteBoundaryWeightObject.squareRepresentative x + x.debtAbsorption =
      FiniteBoundaryWeightObject.finitePartRepresentative x := by
  unfold FiniteBoundaryWeightObject.absorbedSquareRepresentative at h
  unfold FiniteBoundaryWeightObject.squareRepresentative
  exact h.absorbed_square_eq_finitePart

end FiniteBoundaryLowerWeightAbsorptionCert

/-- The completed prime off-diagonal finite-part channel. -/
noncomputable def completedPrimeOffDiagonalChannel
    (f : ZetaAdmissibleFunction) : ℝ :=
  zetaCompletedPrimeOffDiagonalChannel f

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
  have hkernel :
      convolutionAutocorrelationKernel f ι.center =
        zetaSeedInner (zetaTranslate ι.center f) f :=
    convolutionAutocorrelationKernel_eq_translateInner f ι.center
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

/-- The completed spectral prime channel is the real part of the contour-side spectral-sample
prime-power presentation. -/
theorem completedSpectralPrimeOffDiagonalChannel_eq_spectralSampleContribution_re
    (f : ZetaAdmissibleFunction) :
    completedSpectralPrimeOffDiagonalChannel f =
      Complex.re
        (zetaCompletedExplicitFormulaPrimePowerSpectralSampleContribution
          (convolutionAutocorrelation f)) := by
  rfl

/-- The completed prime finite-part channel obtained after finite diagonal-debt cancellation.

There is no standalone completed diagonal-debt summand here: the finite debt and finite
absorption terms cancel before taking the completed prime finite-part limit. -/
noncomputable def completedPrimeDefectKernelRenormalizedChannel
    (f : ZetaAdmissibleFunction) : ℝ :=
  completedPrimeOffDiagonalChannel f

/-- The completed positive prime defect-kernel channel. -/
noncomputable def completedPrimeDefectKernelPositiveChannel
    (f : ZetaAdmissibleFunction) : ℝ :=
  Complex.re (zetaPrimeDefectKernelPositiveForm f)

/-- The completed renormalized boundary channel after passing from the finite triangular
presentation to the positive Hermitian defect-kernel realization.  This is the positive
defect-square channel, not the raw finite-part/off-diagonal boundary scalar. -/
noncomputable def completedRenormalizedDefectKernelBoundaryChannel
    (f : ZetaAdmissibleFunction) : ℝ :=
  completedPrimeDefectKernelPositiveChannel f +
    ZetaHermitianPacketEnsemble.archimedeanPacketGram
      (zetaCompletedHermitianBoundaryDefect f) +
    ZetaHermitianPacketEnsemble.correctionPacketGram
      (zetaCompletedHermitianBoundaryDefect f)

/-- The completed physical finite-part boundary channel.  This is the limit object of the
renormalized square-energy windows before comparing it with the explicit-formula boundary
functional. -/
noncomputable def completedFinitePartBoundaryChannel
    (f : ZetaAdmissibleFunction) : ℝ :=
  completedPrimeDefectKernelRenormalizedChannel f +
    zetaArchimedeanAutocorrelationSquareEnergy f +
    zetaCorrectionAutocorrelationSquareEnergy f

/-- The prime finite-part tail: finite prime off-diagonal window minus the completed prime
off-diagonal channel. -/
def finitePartPrimeTail
    (N : ℕ) (f : ZetaAdmissibleFunction) : ℝ :=
  finitePartPrimeOffDiagonalWindow N f -
    completedPrimeOffDiagonalChannel f

/-- The grouped finite-part tail of the prime defect package: cross term, diagonal debt, and
debt absorption are kept together because the positive prime object is the defect square, not
the raw cross term alone. -/
def finitePartPrimeDefectRenormalizedTail
    (N : ℕ) (f : ZetaAdmissibleFunction) : ℝ :=
  (finitePartPrimeOffDiagonalWindow N f +
      zetaPrimeDiagonalDebt N f +
      finitePartDebtAbsorptionWindow N f) -
    completedPrimeDefectKernelRenormalizedChannel f

/-- The archimedean finite-part tail: the finite archimedean square channel minus the completed
archimedean boundary channel. -/
def finitePartArchimedeanTail
    (_N : ℕ) (f : ZetaAdmissibleFunction) : ℝ :=
  zetaArchimedeanAutocorrelationSquareEnergy f -
    Complex.re (archimedeanBoundaryChannel (convolutionAutocorrelation f))

/-- The pole/completion finite-part tail: the finite correction square channel minus the
completed pole and residual completion channels. -/
def finitePartCorrectionTail
    (_N : ℕ) (f : ZetaAdmissibleFunction) : ℝ :=
  zetaCorrectionAutocorrelationSquareEnergy f -
    Complex.re (poleBoundaryChannel (convolutionAutocorrelation f))

/-- The pole/completion residual tail.  In the current normalization the completion channel is
zero, but it remains a named tail so later refinements of the completed normalization do not
hide pole/completion estimates in the correction theorem. -/
def finitePartPoleTail
    (_N : ℕ) (f : ZetaAdmissibleFunction) : ℝ :=
  - Complex.re (completionBoundaryChannel (convolutionAutocorrelation f))

/-- The total named tail in the finite-part convergence certificate. -/
def finitePartBoundaryTail
    (N : ℕ) (f : ZetaAdmissibleFunction) : ℝ :=
  finitePartPrimeDefectRenormalizedTail N f +
    finitePartArchimedeanTail N f +
    finitePartCorrectionTail N f +
    finitePartPoleTail N f

/-- The literal remainder of the finite-part window after subtracting the completed boundary
channel.  The named tail decomposition refines this remainder into prime, archimedean, and
pole/completion pieces. -/
def finitePartBoundaryRemainder
    (N : ℕ) (f : ZetaAdmissibleFunction) : ℝ :=
  finitePartBoundaryWindow N f -
    completedFinitePartBoundaryChannel f

/-- Four-term subtraction bookkeeping for the finite-part tail certificate. -/
theorem finitePart_three_sub_four_eq_tail_sum
    (P A C p a q r : ℝ) :
    P + A + C - (p + a + q + r) =
      (P - p) + (A - a) + (C - q) + -r := by
  calc
    P + A + C - (p + a + q + r) =
        P + A + C + -(p + a + q + r) := by
      exact sub_eq_add_neg (P + A + C) (p + a + q + r)
    _ = P + A + C + (-(p + a + q) + -r) := by
      exact congrArg
        (fun x : ℝ => P + A + C + x)
        (neg_add (p + a + q) r)
    _ = P + A + C + (-(p + a) + -q + -r) := by
      exact congrArg
        (fun x : ℝ => P + A + C + (x + -r))
        (neg_add (p + a) q)
    _ = P + A + C + ((-p + -a) + -q + -r) := by
      exact congrArg
        (fun x : ℝ => P + A + C + (x + -q + -r))
        (neg_add p a)
    _ = (((P + A + C) + -p) + -a) + -q + -r := by
      calc
        P + A + C + ((-p + -a) + -q + -r) =
            (P + A + C + ((-p + -a) + -q)) + -r := by
          exact (add_assoc (P + A + C) ((-p + -a) + -q) (-r)).symm
        _ = ((P + A + C + (-p + -a)) + -q) + -r := by
          exact congrArg (fun x : ℝ => x + -r)
            ((add_assoc (P + A + C) (-p + -a) (-q)).symm)
        _ = (((P + A + C) + -p) + -a) + -q + -r := by
          exact congrArg (fun x : ℝ => (x + -q) + -r)
            ((add_assoc (P + A + C) (-p) (-a)).symm)
    _ = (((P + -p) + A + C) + -a) + -q + -r := by
      have hmove :
          (P + A + C) + -p = (P + -p) + A + C := by
        calc
          (P + A + C) + -p = ((P + A) + C) + -p := by
            rfl
          _ = (P + A) + (C + -p) := by
            exact add_assoc (P + A) C (-p)
          _ = (P + A) + (-p + C) := by
            exact congrArg (fun x : ℝ => (P + A) + x) (add_comm C (-p))
          _ = ((P + A) + -p) + C := by
            exact (add_assoc (P + A) (-p) C).symm
          _ = (P + (A + -p)) + C := by
            exact congrArg (fun x : ℝ => x + C) (add_assoc P A (-p))
          _ = (P + (-p + A)) + C := by
            exact congrArg (fun x : ℝ => (P + x) + C) (add_comm A (-p))
          _ = ((P + -p) + A) + C := by
            exact congrArg (fun x : ℝ => x + C) ((add_assoc P (-p) A).symm)
          _ = (P + -p) + A + C := by
            rfl
      exact congrArg (fun x : ℝ => ((x + -a) + -q) + -r) hmove
    _ = ((P - p + A + C) + -a) + -q + -r := by
      exact congrArg (fun x : ℝ => ((x + A + C + -a) + -q) + -r)
        (sub_eq_add_neg P p).symm
    _ = (P - p + (A + -a) + C) + -q + -r := by
      have hmove :
          (P - p + A + C) + -a = P - p + (A + -a) + C := by
        calc
          (P - p + A + C) + -a = ((P - p + A) + C) + -a := by
            rfl
          _ = (P - p + A) + (C + -a) := by
            exact add_assoc (P - p + A) C (-a)
          _ = (P - p + A) + (-a + C) := by
            exact congrArg (fun x : ℝ => (P - p + A) + x) (add_comm C (-a))
          _ = ((P - p + A) + -a) + C := by
            exact (add_assoc (P - p + A) (-a) C).symm
          _ = (P - p + (A + -a)) + C := by
            exact congrArg (fun x : ℝ => x + C) (add_assoc (P - p) A (-a))
          _ = P - p + (A + -a) + C := by
            rfl
      exact congrArg (fun x : ℝ => (x + -q) + -r) hmove
    _ = (P - p + (A - a) + C) + -q + -r := by
      exact congrArg (fun x : ℝ => (P - p + x + C + -q) + -r)
        (sub_eq_add_neg A a).symm
    _ = (P - p + (A - a) + (C + -q)) + -r := by
      exact congrArg (fun x : ℝ => x + -r)
        (add_assoc (P - p + (A - a)) C (-q))
    _ = (P - p + (A - a) + (C - q)) + -r := by
      exact congrArg (fun x : ℝ => (P - p + (A - a) + x) + -r)
        (sub_eq_add_neg C q).symm
    _ = (P - p) + (A - a) + (C - q) + -r := by
      rfl

/-- Diagonal debt cancellation is algebraic and happens before taking the finite-part limit. -/
theorem completedBoundaryWindow_add_diagonalDebt_sub_diagonalDebt
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    completedBoundaryWindow N f + zetaPrimeDiagonalDebt N f -
        zetaPrimeDiagonalDebt N f =
      completedBoundaryWindow N f := by
  have hcancel :
      zetaPrimeDiagonalDebt N f + -zetaPrimeDiagonalDebt N f = 0 := by
    exact add_neg_cancel (zetaPrimeDiagonalDebt N f)
  calc
    completedBoundaryWindow N f + zetaPrimeDiagonalDebt N f -
        zetaPrimeDiagonalDebt N f =
        completedBoundaryWindow N f + zetaPrimeDiagonalDebt N f +
          -zetaPrimeDiagonalDebt N f := by
      exact sub_eq_add_neg
        (completedBoundaryWindow N f + zetaPrimeDiagonalDebt N f)
        (zetaPrimeDiagonalDebt N f)
    _ =
        completedBoundaryWindow N f +
          (zetaPrimeDiagonalDebt N f + -zetaPrimeDiagonalDebt N f) := by
      exact add_assoc
        (completedBoundaryWindow N f)
        (zetaPrimeDiagonalDebt N f)
        (-zetaPrimeDiagonalDebt N f)
    _ = completedBoundaryWindow N f + 0 := by
      exact congrArg (fun x : ℝ => completedBoundaryWindow N f + x) hcancel
    _ = completedBoundaryWindow N f := by
      exact add_zero (completedBoundaryWindow N f)

/-- The finite-part window is the completed boundary channel plus its literal remainder. -/
theorem finitePartBoundaryWindow_eq_boundaryChannel_add_remainder
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    finitePartBoundaryWindow N f =
      completedFinitePartBoundaryChannel f +
        finitePartBoundaryRemainder N f := by
  unfold finitePartBoundaryRemainder
  exact zetaBoundaryDebt_add_sub_cancel
    (finitePartBoundaryWindow N f)
    (completedFinitePartBoundaryChannel f)

/-- The named finite-part tails assemble to the literal boundary remainder.  This is the
finite-part cancellation certificate: the prime-defect package is kept grouped as cross term,
diagonal debt, and debt absorption, while archimedean, correction, and completion tails remain
separate. -/
theorem finitePartBoundaryRemainder_eq_tail
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    finitePartBoundaryRemainder N f =
      finitePartBoundaryTail N f := by
  let g : ZetaAdmissibleFunction := convolutionAutocorrelation f
  let P : ℝ :=
    finitePartPrimeOffDiagonalWindow N f +
      zetaPrimeDiagonalDebt N f +
      finitePartDebtAbsorptionWindow N f
  let A : ℝ := zetaArchimedeanAutocorrelationSquareEnergy f
  let C : ℝ := zetaCorrectionAutocorrelationSquareEnergy f
  let p : ℝ :=
    completedPrimeDefectKernelRenormalizedChannel f
  let a : ℝ := Complex.re (archimedeanBoundaryChannel g)
  let q : ℝ := Complex.re (poleBoundaryChannel g)
  let r : ℝ := Complex.re (completionBoundaryChannel g)
  have hfinite :
      finitePartBoundaryWindow N f = P + A + C := by
    unfold finitePartBoundaryWindow
    unfold finitePartPrimeOffDiagonalWindow
    unfold finitePartArchimedeanCorrectionWindow
    unfold finitePartDebtAbsorptionWindow
    unfold zetaArchimedeanCorrectionAutocorrelationChannel
    calc
      zetaPrimeOffDiagonalChannel N f + zetaPrimeDiagonalDebt N f +
          -zetaPrimeDiagonalDebt N f +
          zetaArchimedeanCorrectionAutocorrelationChannel f =
          (zetaPrimeOffDiagonalChannel N f + zetaPrimeDiagonalDebt N f +
            -zetaPrimeDiagonalDebt N f) +
            zetaArchimedeanCorrectionAutocorrelationChannel f := by
        rfl
      _ =
          (zetaPrimeOffDiagonalChannel N f + zetaPrimeDiagonalDebt N f +
            -zetaPrimeDiagonalDebt N f) +
            (zetaArchimedeanAutocorrelationSquareEnergy f +
              zetaCorrectionAutocorrelationSquareEnergy f) := by
        exact congrArg
          (fun x : ℝ =>
            (zetaPrimeOffDiagonalChannel N f + zetaPrimeDiagonalDebt N f +
              -zetaPrimeDiagonalDebt N f) + x)
          (zetaArchimedeanCorrectionAutocorrelationChannel_eq_squareEnergy f)
      _ = P + A + C := by
        rfl
  have hchannel :
      completedFinitePartBoundaryChannel f = p + a + q + r := by
    have harch :
        a = A := by
      unfold a
      unfold g
      unfold archimedeanBoundaryChannel
      exact zetaArchimedeanAutocorrelationChannel_eq_squareEnergy f
    have hcorr :
        q = C := by
      unfold q
      unfold g
      unfold poleBoundaryChannel
      exact zetaCorrectionAutocorrelationChannel_eq_squareEnergy f
    have hr :
        r = 0 := by
      unfold r
      unfold g
      unfold completionBoundaryChannel
      exact Complex.zero_re
    unfold completedFinitePartBoundaryChannel
    calc
      completedPrimeOffDiagonalChannel f +
          zetaArchimedeanAutocorrelationSquareEnergy f +
          zetaCorrectionAutocorrelationSquareEnergy f =
          p + A + C := by
        unfold p
        unfold completedPrimeDefectKernelRenormalizedChannel
        rfl
      _ = p + a + C := by
        exact congrArg (fun x : ℝ => p + x + C) harch.symm
      _ = p + a + q := by
        exact congrArg (fun x : ℝ => p + a + x) hcorr.symm
      _ = p + a + q + 0 := by
        exact (add_zero (p + a + q)).symm
      _ = p + a + q + r := by
        exact congrArg (fun x : ℝ => p + a + q + x) hr.symm
  unfold finitePartBoundaryRemainder
  unfold finitePartBoundaryTail
  unfold finitePartPrimeDefectRenormalizedTail
  unfold finitePartArchimedeanTail
  unfold finitePartCorrectionTail
  unfold finitePartPoleTail
  change finitePartBoundaryWindow N f - completedFinitePartBoundaryChannel f =
    (P - p) + (A - a) + (C - q) + -r
  calc
    finitePartBoundaryWindow N f - completedFinitePartBoundaryChannel f =
        (P + A + C) - completedFinitePartBoundaryChannel f := by
      exact congrArg (fun x : ℝ => x - completedFinitePartBoundaryChannel f) hfinite
    _ = (P + A + C) - (p + a + q + r) := by
      exact congrArg (fun x : ℝ => (P + A + C) - x) hchannel
    _ = (P - p) + (A - a) + (C - q) + -r := by
      exact finitePart_three_sub_four_eq_tail_sum P A C p a q r

/-- The prime off-diagonal coordinates are summable against the completed prime-power weights.
This is the exact admissibility/decay input needed for the completed prime finite-part limit. -/
theorem summable_primeOffDiagonalCoordinate
    (f : ZetaAdmissibleFunction) :
    Summable (fun ι : ZetaPrimePowerIndex =>
      zetaPrimeOffDiagonalCoordinate ι f) := by
  exact summable_zetaPrimeOffDiagonalCoordinate f

/-- The growing finite prime off-diagonal windows converge to the completed prime off-diagonal
channel.  This is the window-exhaustion theorem built from prime weighted-kernel summability
and the completed-prime realization theorem. -/
theorem zetaPrimeOffDiagonalChannel_tendsto_completedPrimeOffDiagonalChannel
    (f : ZetaAdmissibleFunction) :
    Tendsto
      (fun N : ℕ => zetaPrimeOffDiagonalChannel N f)
      atTop
      (𝓝 (completedPrimeOffDiagonalChannel f)) := by
  unfold completedPrimeOffDiagonalChannel
  exact zetaPrimeOffDiagonalChannel_tendsto_completed f

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

/-- Prime/off-diagonal finite-part tails tend to zero because the growing finite prime windows
converge to the completed prime translation-defect energy.  The analytic content is the
preceding completed-prime convergence theorem. -/
theorem finitePartPrimeTail_tendsto_zero
    (f : ZetaAdmissibleFunction) :
    Tendsto (fun N : ℕ => finitePartPrimeTail N f) atTop (𝓝 0) := by
  have hprime :
      Tendsto
        (fun N : ℕ => zetaPrimeOffDiagonalChannel N f)
        atTop
        (𝓝 (completedPrimeOffDiagonalChannel f)) :=
    zetaPrimeOffDiagonalChannel_tendsto_completedPrimeOffDiagonalChannel f
  have htail :
      Tendsto
        (fun N : ℕ =>
          zetaPrimeOffDiagonalChannel N f -
            completedPrimeOffDiagonalChannel f)
        atTop
        (𝓝 (completedPrimeOffDiagonalChannel f -
          completedPrimeOffDiagonalChannel f)) := by
    exact hprime.sub tendsto_const_nhds
  have hzero :
      completedPrimeOffDiagonalChannel f -
        completedPrimeOffDiagonalChannel f = 0 := by
    exact sub_self (completedPrimeOffDiagonalChannel f)
  unfold finitePartPrimeTail
  unfold finitePartPrimeOffDiagonalWindow
  exact Eq.subst
    (motive := fun x : ℝ =>
      Tendsto
        (fun N : ℕ =>
          zetaPrimeOffDiagonalChannel N f -
            completedPrimeOffDiagonalChannel f)
        atTop (𝓝 x))
    hzero
    htail

/-- A real limit of nonnegative finite windows is nonnegative. -/
theorem nonnegative_of_tendsto_nonnegative_owner
    {u : ℕ → ℝ} {x : ℝ}
    (hu : Tendsto u atTop (𝓝 x))
    (hnonneg : ∀ N : ℕ, 0 ≤ u N) :
    0 ≤ x := by
  have hclosed : IsClosed (Set.Ici (0 : ℝ)) :=
    isClosed_Ici
  have heventually : ∀ᶠ N in atTop, u N ∈ Set.Ici (0 : ℝ) :=
    Filter.Eventually.of_forall
      (fun N : ℕ => hnonneg N)
  exact hclosed.mem_of_tendsto hu heventually

/-- Debt and debt-absorption cancel in each finite prime-defect renormalized window. -/
theorem finitePartPrimeDefectRenormalizedWindow_eq_primeOffDiagonalWindow
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    finitePartPrimeOffDiagonalWindow N f +
        zetaPrimeDiagonalDebt N f +
        finitePartDebtAbsorptionWindow N f =
      finitePartPrimeOffDiagonalWindow N f := by
  unfold finitePartDebtAbsorptionWindow
  let P : ℝ := finitePartPrimeOffDiagonalWindow N f
  let D : ℝ := zetaPrimeDiagonalDebt N f
  change P + D + -D = P
  have hcancel : D + -D = 0 := by
    exact add_neg_cancel D
  calc
    P + D + -D = P + (D + -D) := by
      exact add_assoc P D (-D)
    _ = P + 0 := by
      exact congrArg (fun x : ℝ => P + x) hcancel
    _ = P := by
      exact add_zero P

/-- The completed renormalized prime-defect package is exactly the completed prime
off-diagonal finite part. -/
theorem completedPrimeDefectKernelRenormalizedChannel_eq_primeOffDiagonalChannel
    (f : ZetaAdmissibleFunction) :
    completedPrimeDefectKernelRenormalizedChannel f =
      completedPrimeOffDiagonalChannel f := by
  rfl

/-- The grouped prime-defect renormalized tail tends to zero. -/
theorem finitePartPrimeDefectRenormalizedTail_tendsto_zero
    (f : ZetaAdmissibleFunction) :
    Tendsto (fun N : ℕ => finitePartPrimeDefectRenormalizedTail N f) atTop (𝓝 0) := by
  have hprime : Tendsto (fun N : ℕ => finitePartPrimeTail N f) atTop (𝓝 0) :=
    finitePartPrimeTail_tendsto_zero f
  have hfun :
      (fun N : ℕ => finitePartPrimeDefectRenormalizedTail N f) =
        (fun N : ℕ => finitePartPrimeTail N f) := by
    funext N
    have hcancel :=
      finitePartPrimeDefectRenormalizedWindow_eq_primeOffDiagonalWindow N f
    unfold finitePartPrimeDefectRenormalizedTail
    unfold finitePartPrimeTail
    let P : ℝ := finitePartPrimeOffDiagonalWindow N f
    let D : ℝ := zetaPrimeDiagonalDebt N f
    let E : ℝ := finitePartDebtAbsorptionWindow N f
    let p : ℝ := completedPrimeOffDiagonalChannel f
    change (P + D + E) - completedPrimeDefectKernelRenormalizedChannel f = P - p
    have hrenorm :
        completedPrimeDefectKernelRenormalizedChannel f = p :=
      completedPrimeDefectKernelRenormalizedChannel_eq_primeOffDiagonalChannel f
    have hfinite : P + D + E = P := hcancel
    calc
      (P + D + E) - completedPrimeDefectKernelRenormalizedChannel f =
          P - completedPrimeDefectKernelRenormalizedChannel f := by
        exact congrArg
          (fun x : ℝ => x - completedPrimeDefectKernelRenormalizedChannel f)
          hfinite
      _ = P - p := by
        exact congrArg (fun x : ℝ => P - x) hrenorm
  exact Eq.subst
    (motive := fun u : ℕ → ℝ => Tendsto u atTop (𝓝 0))
    hfun.symm
    hprime

/-- In the current completed normalization the archimedean finite-part tail is identically
zero: the finite square channel is exactly the archimedean channel on the autocorrelation
probe. -/
theorem finitePartArchimedeanTail_eq_zero
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    finitePartArchimedeanTail N f = 0 := by
  have harch :
      Complex.re (archimedeanBoundaryChannel (convolutionAutocorrelation f)) =
        zetaArchimedeanAutocorrelationSquareEnergy f := by
    unfold archimedeanBoundaryChannel
    exact zetaArchimedeanAutocorrelationChannel_eq_squareEnergy f
  unfold finitePartArchimedeanTail
  calc
    zetaArchimedeanAutocorrelationSquareEnergy f -
        Complex.re (archimedeanBoundaryChannel (convolutionAutocorrelation f)) =
        zetaArchimedeanAutocorrelationSquareEnergy f -
          zetaArchimedeanAutocorrelationSquareEnergy f := by
      exact congrArg
        (fun x : ℝ => zetaArchimedeanAutocorrelationSquareEnergy f - x)
        harch
    _ = 0 := by
      exact sub_self (zetaArchimedeanAutocorrelationSquareEnergy f)

/-- Archimedean finite-part tails tend to zero by the completed archimedean kernel bound and
integrable-tail convergence. -/
theorem finitePartArchimedeanTail_tendsto_zero
    (f : ZetaAdmissibleFunction) :
    Tendsto (fun N : ℕ => finitePartArchimedeanTail N f) atTop (𝓝 0) := by
  have hfun :
      (fun N : ℕ => finitePartArchimedeanTail N f) =
        (fun _N : ℕ => (0 : ℝ)) := by
    funext N
    exact finitePartArchimedeanTail_eq_zero N f
  exact Eq.subst
    (motive := fun u : ℕ → ℝ => Tendsto u atTop (𝓝 0))
    hfun.symm
    tendsto_const_nhds

/-- In the current completed normalization the correction finite-part tail is identically
zero: the correction square energy is the completed pole correction on the autocorrelation
probe.  Diagonal-debt absorption is handled by its own channel. -/
theorem finitePartCorrectionTail_eq_zero
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    finitePartCorrectionTail N f = 0 := by
  have hcorr :
      Complex.re (poleBoundaryChannel (convolutionAutocorrelation f)) =
        zetaCorrectionAutocorrelationSquareEnergy f := by
    unfold poleBoundaryChannel
    exact zetaCorrectionAutocorrelationChannel_eq_squareEnergy f
  unfold finitePartCorrectionTail
  calc
    zetaCorrectionAutocorrelationSquareEnergy f -
        Complex.re (poleBoundaryChannel (convolutionAutocorrelation f)) =
        zetaCorrectionAutocorrelationSquareEnergy f -
          zetaCorrectionAutocorrelationSquareEnergy f := by
      exact congrArg
        (fun x : ℝ => zetaCorrectionAutocorrelationSquareEnergy f - x)
        hcorr
    _ = 0 := by
      exact sub_self (zetaCorrectionAutocorrelationSquareEnergy f)

/-- Correction finite-part tails tend to zero. -/
theorem finitePartCorrectionTail_tendsto_zero
    (f : ZetaAdmissibleFunction) :
    Tendsto (fun N : ℕ => finitePartCorrectionTail N f) atTop (𝓝 0) := by
  have hfun :
      (fun N : ℕ => finitePartCorrectionTail N f) =
        (fun _N : ℕ => (0 : ℝ)) := by
    funext N
    exact finitePartCorrectionTail_eq_zero N f
  exact Eq.subst
    (motive := fun u : ℕ → ℝ => Tendsto u atTop (𝓝 0))
    hfun.symm
    tendsto_const_nhds

/-- In the current completed normalization the residual completion tail is identically zero. -/
theorem finitePartPoleTail_eq_zero
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    finitePartPoleTail N f = 0 := by
  have hcompletion :
      completionBoundaryChannel (convolutionAutocorrelation f) = 0 := by
    unfold completionBoundaryChannel
    rfl
  have hreal :
      Complex.re (completionBoundaryChannel (convolutionAutocorrelation f)) = 0 := by
    calc
      Complex.re (completionBoundaryChannel (convolutionAutocorrelation f)) =
          Complex.re 0 := by
        exact congrArg Complex.re hcompletion
      _ = 0 := by
        exact Complex.zero_re
  unfold finitePartPoleTail
  calc
    -Complex.re (completionBoundaryChannel (convolutionAutocorrelation f)) =
        -0 := by
      exact congrArg Neg.neg hreal
    _ = 0 := by
      exact neg_zero

/-- Pole/completion finite-part tails tend to zero by the pole-kernel tail estimate. -/
theorem finitePartPoleTail_tendsto_zero
    (f : ZetaAdmissibleFunction) :
    Tendsto (fun N : ℕ => finitePartPoleTail N f) atTop (𝓝 0) := by
  have hfun :
      (fun N : ℕ => finitePartPoleTail N f) =
        (fun _N : ℕ => (0 : ℝ)) := by
    funext N
    exact finitePartPoleTail_eq_zero N f
  exact Eq.subst
    (motive := fun u : ℕ → ℝ => Tendsto u atTop (𝓝 0))
    hfun.symm
    tendsto_const_nhds

/-- The explicit total finite-part tail tends to zero once its four named channel tails do. -/
theorem finitePartBoundaryTail_tendsto_zero
    (f : ZetaAdmissibleFunction) :
    Tendsto (fun N : ℕ => finitePartBoundaryTail N f) atTop (𝓝 0) := by
  have hprime :
      Tendsto (fun N : ℕ => finitePartPrimeDefectRenormalizedTail N f) atTop (𝓝 0) :=
    finitePartPrimeDefectRenormalizedTail_tendsto_zero f
  have harch : Tendsto (fun N : ℕ => finitePartArchimedeanTail N f) atTop (𝓝 0) :=
    finitePartArchimedeanTail_tendsto_zero f
  have hcorr : Tendsto (fun N : ℕ => finitePartCorrectionTail N f) atTop (𝓝 0) :=
    finitePartCorrectionTail_tendsto_zero f
  have hpole : Tendsto (fun N : ℕ => finitePartPoleTail N f) atTop (𝓝 0) :=
    finitePartPoleTail_tendsto_zero f
  have hprime_arch :
      Tendsto
        (fun N : ℕ =>
          finitePartPrimeDefectRenormalizedTail N f + finitePartArchimedeanTail N f)
        atTop (𝓝 (0 + 0)) := by
    exact hprime.add harch
  have hprime_arch_zero :
      Tendsto
        (fun N : ℕ =>
          finitePartPrimeDefectRenormalizedTail N f + finitePartArchimedeanTail N f)
        atTop (𝓝 0) := by
    exact Eq.subst
      (motive := fun x : ℝ =>
        Tendsto
          (fun N : ℕ =>
            finitePartPrimeDefectRenormalizedTail N f + finitePartArchimedeanTail N f)
          atTop (𝓝 x))
      (add_zero 0)
      hprime_arch
  have hthree :
      Tendsto
        (fun N : ℕ =>
          finitePartPrimeDefectRenormalizedTail N f + finitePartArchimedeanTail N f +
            finitePartCorrectionTail N f)
        atTop (𝓝 (0 + 0)) := by
    exact hprime_arch_zero.add hcorr
  have hthree_zero :
      Tendsto
        (fun N : ℕ =>
          finitePartPrimeDefectRenormalizedTail N f + finitePartArchimedeanTail N f +
            finitePartCorrectionTail N f)
        atTop (𝓝 0) := by
    exact Eq.subst
      (motive := fun x : ℝ =>
        Tendsto
          (fun N : ℕ =>
            finitePartPrimeDefectRenormalizedTail N f + finitePartArchimedeanTail N f +
              finitePartCorrectionTail N f)
          atTop (𝓝 x))
      (add_zero 0)
      hthree
  unfold finitePartBoundaryTail
  have hall :
      Tendsto
        (fun N : ℕ =>
          finitePartPrimeDefectRenormalizedTail N f + finitePartArchimedeanTail N f +
            finitePartCorrectionTail N f + finitePartPoleTail N f)
        atTop (𝓝 (0 + 0)) := by
    exact hthree_zero.add hpole
  exact Eq.subst
    (motive := fun x : ℝ =>
      Tendsto
        (fun N : ℕ =>
          finitePartPrimeDefectRenormalizedTail N f + finitePartArchimedeanTail N f +
            finitePartCorrectionTail N f + finitePartPoleTail N f)
        atTop (𝓝 x))
    (add_zero 0)
    hall

/-- The literal finite-part remainder tends to zero because the named tail certificate tends to
zero. -/
theorem finitePartBoundaryRemainder_tendsto_zero
    (f : ZetaAdmissibleFunction) :
    Tendsto (fun N : ℕ => finitePartBoundaryRemainder N f) atTop (𝓝 0) := by
  have htail : Tendsto (fun N : ℕ => finitePartBoundaryTail N f) atTop (𝓝 0) :=
    finitePartBoundaryTail_tendsto_zero f
  have hrem :
      (fun N : ℕ => finitePartBoundaryRemainder N f) =
        (fun N : ℕ => finitePartBoundaryTail N f) := by
    funext N
    exact finitePartBoundaryRemainder_eq_tail N f
  exact Eq.subst
    (motive := fun u : ℕ → ℝ => Tendsto u atTop (𝓝 0))
    hrem.symm
    htail

/-- The completed corrected boundary window is the finite completed square energy. -/
theorem completedCorrectedBoundaryWindow_eq_squareEnergy
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    completedCorrectedBoundaryWindow N f =
      zetaCompletedPhysicalAutocorrelationSquareEnergy N f := by
  unfold completedCorrectedBoundaryWindow
  unfold completedBoundaryWindow
  exact zetaCompletedPhysicalAutocorrelationBoundaryChannel_add_diagonalDebt_eq_squareEnergy N f

/-- The completed corrected boundary window is the finite positive square-energy window. -/
theorem completedCorrectedBoundaryWindow_eq_finitePositiveSquareEnergyWindow
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    completedCorrectedBoundaryWindow N f =
      finitePositiveSquareEnergyWindow N f := by
  unfold finitePositiveSquareEnergyWindow
  exact completedCorrectedBoundaryWindow_eq_squareEnergy N f

/-- The finite positive square-energy window is nonnegative. -/
theorem finitePositiveSquareEnergyWindow_nonnegative
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    0 ≤ finitePositiveSquareEnergyWindow N f := by
  unfold finitePositiveSquareEnergyWindow
  unfold zetaCompletedPhysicalAutocorrelationSquareEnergy
  exact add_nonneg
    (zetaPrimeTranslationDefectEnergy_nonnegative N f)
    (zetaArchimedeanCorrectionAutocorrelationSquareEnergy_nonnegative f)

/-- The finite-part boundary window is the raw completed physical boundary window after the
finite diagonal debt has been added and cancelled inside the completed normalization. -/
theorem finitePartBoundaryWindow_eq_completedBoundaryWindow
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    finitePartBoundaryWindow N f =
      completedBoundaryWindow N f := by
  unfold finitePartBoundaryWindow
  unfold finitePartPrimeOffDiagonalWindow
  unfold finitePartArchimedeanCorrectionWindow
  unfold finitePartDebtAbsorptionWindow
  unfold completedBoundaryWindow
  unfold zetaCompletedPhysicalAutocorrelationBoundaryChannel
  unfold zetaArchimedeanCorrectionAutocorrelationChannel
  let P : ℝ := zetaPrimeOffDiagonalChannel N f
  let D : ℝ := zetaPrimeDiagonalDebt N f
  let A : ℝ := zetaArchimedeanCorrectionAutocorrelationChannel f
  have hcancel : D + -D = 0 := by
    exact add_neg_cancel D
  calc
    P + D + -D + A =
        P + (D + -D) + A := by
      exact congrArg (fun x : ℝ => x + A) (add_assoc P D (-D))
    _ = P + 0 + A := by
      exact congrArg (fun x : ℝ => P + x + A)
        hcancel
    _ = P + A := by
      exact congrArg (fun x : ℝ => x + A) (add_zero P)

/-- The positive corrected window plus its finite debt absorption is exactly the finite-part
boundary window. -/
theorem finitePositiveRenormalizedBoundaryWindow_eq_finitePartBoundaryWindow
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    finitePositiveRenormalizedBoundaryWindow N f =
      finitePartBoundaryWindow N f := by
  unfold finitePositiveRenormalizedBoundaryWindow
  unfold completedCorrectedBoundaryWindow
  unfold finitePartDebtAbsorptionWindow
  have hsub :
      completedBoundaryWindow N f + zetaPrimeDiagonalDebt N f +
          -zetaPrimeDiagonalDebt N f =
        completedBoundaryWindow N f + zetaPrimeDiagonalDebt N f -
          zetaPrimeDiagonalDebt N f := by
    exact (sub_eq_add_neg
      (completedBoundaryWindow N f + zetaPrimeDiagonalDebt N f)
      (zetaPrimeDiagonalDebt N f)).symm
  calc
    completedBoundaryWindow N f + zetaPrimeDiagonalDebt N f +
        -zetaPrimeDiagonalDebt N f =
        completedBoundaryWindow N f + zetaPrimeDiagonalDebt N f -
          zetaPrimeDiagonalDebt N f := hsub
    _ = completedBoundaryWindow N f := by
      exact completedBoundaryWindow_add_diagonalDebt_sub_diagonalDebt N f
    _ = finitePartBoundaryWindow N f := by
      exact (finitePartBoundaryWindow_eq_completedBoundaryWindow N f).symm

/-- The finite boundary weight object's square representative is the positive square-energy
window. -/
theorem finiteBoundaryWeightObject_squareRepresentative_eq_squareEnergyWindow
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    FiniteBoundaryWeightObject.squareRepresentative
        (finiteBoundaryWeightObject N f) =
      finitePositiveSquareEnergyWindow N f := by
  rfl

/-- The square representative of the finite boundary weight object is nonnegative. -/
theorem finiteBoundaryWeightObject_squareRepresentative_nonnegative
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    0 ≤
      FiniteBoundaryWeightObject.squareRepresentative
        (finiteBoundaryWeightObject N f) := by
  unfold FiniteBoundaryWeightObject.squareRepresentative
  unfold finiteBoundaryWeightObject
  unfold finitePositiveSquareEnergyWindow
  unfold zetaCompletedPhysicalAutocorrelationSquareEnergy
  exact add_nonneg
    (zetaPrimeTranslationDefectEnergy_nonnegative N f)
    (zetaArchimedeanCorrectionAutocorrelationSquareEnergy_nonnegative f)

/-- The finite boundary weight object's finite-part representative is the finite-part
boundary window. -/
theorem finiteBoundaryWeightObject_finitePartRepresentative_eq_finitePartBoundaryWindow
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    FiniteBoundaryWeightObject.finitePartRepresentative
        (finiteBoundaryWeightObject N f) =
      finitePartBoundaryWindow N f := by
  rfl

/-- The finite boundary weight object's absorbed square representative is the positive
renormalized boundary window. -/
theorem finiteBoundaryWeightObject_absorbedSquareRepresentative_eq_renormalizedWindow
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    FiniteBoundaryWeightObject.absorbedSquareRepresentative
        (finiteBoundaryWeightObject N f) =
      finitePositiveRenormalizedBoundaryWindow N f := by
  unfold FiniteBoundaryWeightObject.absorbedSquareRepresentative
  unfold finiteBoundaryWeightObject
  unfold finitePositiveRenormalizedBoundaryWindow
  have hcorrected :
      completedCorrectedBoundaryWindow N f =
        finitePositiveSquareEnergyWindow N f :=
    completedCorrectedBoundaryWindow_eq_finitePositiveSquareEnergyWindow N f
  calc
    finitePositiveSquareEnergyWindow N f + finitePartDebtAbsorptionWindow N f =
        completedCorrectedBoundaryWindow N f + finitePartDebtAbsorptionWindow N f := by
      exact congrArg
        (fun x : ℝ => x + finitePartDebtAbsorptionWindow N f)
        hcorrected.symm

/-- The diagonal debt and its absorption channel cancel inside the finite boundary weight
object. -/
theorem finiteBoundaryWeightObject_debt_absorption_cancel
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    (finiteBoundaryWeightObject N f).diagonalDebt +
        (finiteBoundaryWeightObject N f).debtAbsorption =
      0 := by
  unfold finiteBoundaryWeightObject
  unfold finitePartDebtAbsorptionWindow
  exact add_neg_cancel (zetaPrimeDiagonalDebt N f)

/-- The concrete finite lower-weight exact representative is zero. -/
theorem finiteBoundaryWeightObject_lowerWeightExactRepresentative_eq_zero
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    FiniteBoundaryWeightObject.lowerWeightExactRepresentative
        (finiteBoundaryWeightObject N f) =
      0 := by
  unfold FiniteBoundaryWeightObject.lowerWeightExactRepresentative
  exact finiteBoundaryWeightObject_debt_absorption_cancel N f

/-- The finite absorption channel is the negative face of the finite diagonal debt. -/
theorem finiteBoundaryWeightObject_debtAbsorption_eq_neg_diagonalDebt
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    (finiteBoundaryWeightObject N f).debtAbsorption =
      - (finiteBoundaryWeightObject N f).diagonalDebt := by
  unfold finiteBoundaryWeightObject
  unfold finitePartDebtAbsorptionWindow
  rfl

/-- The absorbed square representative equals the finite-part representative.  This is the
finite triangular transport identity: the positive square is transported to the finite-part
window by adding the lower-weight debt absorption channel. -/
theorem finiteBoundaryWeightObject_absorbedSquare_eq_finitePartRepresentative
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    FiniteBoundaryWeightObject.absorbedSquareRepresentative
        (finiteBoundaryWeightObject N f) =
      FiniteBoundaryWeightObject.finitePartRepresentative
        (finiteBoundaryWeightObject N f) := by
  exact
    (finiteBoundaryWeightObject_absorbedSquareRepresentative_eq_renormalizedWindow
      N f).trans
      ((finitePositiveRenormalizedBoundaryWindow_eq_finitePartBoundaryWindow N f).trans
        (finiteBoundaryWeightObject_finitePartRepresentative_eq_finitePartBoundaryWindow
          N f).symm)

/-- Weight-triangular transport at a finite cutoff: adding the absorption face to the positive
square representative gives the finite-part representative. -/
theorem finiteBoundaryWeightObject_weightTriangularTransport
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    FiniteBoundaryWeightObject.squareRepresentative
        (finiteBoundaryWeightObject N f) +
      (finiteBoundaryWeightObject N f).debtAbsorption =
    FiniteBoundaryWeightObject.finitePartRepresentative
        (finiteBoundaryWeightObject N f) := by
  exact finiteBoundaryWeightObject_absorbedSquare_eq_finitePartRepresentative N f

/-- The finite triangular transport may equivalently replace the diagonal face by its
lower-weight exact absorption partner. -/
theorem finiteBoundaryWeightObject_square_add_neg_diagonalDebt_eq_finitePartRepresentative
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    FiniteBoundaryWeightObject.squareRepresentative
        (finiteBoundaryWeightObject N f) -
      (finiteBoundaryWeightObject N f).diagonalDebt =
    FiniteBoundaryWeightObject.finitePartRepresentative
        (finiteBoundaryWeightObject N f) := by
  have habs :
      (finiteBoundaryWeightObject N f).debtAbsorption =
        - (finiteBoundaryWeightObject N f).diagonalDebt :=
    finiteBoundaryWeightObject_debtAbsorption_eq_neg_diagonalDebt N f
  calc
    FiniteBoundaryWeightObject.squareRepresentative
        (finiteBoundaryWeightObject N f) -
      (finiteBoundaryWeightObject N f).diagonalDebt =
        FiniteBoundaryWeightObject.squareRepresentative
          (finiteBoundaryWeightObject N f) +
        - (finiteBoundaryWeightObject N f).diagonalDebt := by
      exact sub_eq_add_neg
        (FiniteBoundaryWeightObject.squareRepresentative
          (finiteBoundaryWeightObject N f))
        ((finiteBoundaryWeightObject N f).diagonalDebt)
    _ =
        FiniteBoundaryWeightObject.squareRepresentative
          (finiteBoundaryWeightObject N f) +
        (finiteBoundaryWeightObject N f).debtAbsorption := by
      exact congrArg
        (fun x : ℝ =>
          FiniteBoundaryWeightObject.squareRepresentative
            (finiteBoundaryWeightObject N f) + x)
        habs.symm
    _ =
        FiniteBoundaryWeightObject.finitePartRepresentative
          (finiteBoundaryWeightObject N f) := by
      exact finiteBoundaryWeightObject_weightTriangularTransport N f

/-- The concrete lower-weight absorption certificate for the finite boundary weight object. -/
def finiteBoundaryWeightObject_lowerWeightAbsorptionCert
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    FiniteBoundaryLowerWeightAbsorptionCert (finiteBoundaryWeightObject N f) :=
  { debt_absorption_cancel :=
      finiteBoundaryWeightObject_debt_absorption_cancel N f
    absorbed_square_eq_finitePart :=
      finiteBoundaryWeightObject_absorbedSquare_eq_finitePartRepresentative N f }

/-- The finite diagonal-debt absorption defect: the difference between the absorbed positive
window and the original positive square-energy window. -/
def finiteDiagonalDebtAbsorptionDefect
    (N : ℕ) (f : ZetaAdmissibleFunction) : ℝ :=
  finitePositiveRenormalizedBoundaryWindow N f -
    finitePositiveSquareEnergyWindow N f

/-- The finite absorption defect is exactly the finite debt-absorption channel. -/
theorem finiteDiagonalDebtAbsorptionDefect_eq_finitePartDebtAbsorptionWindow
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    finiteDiagonalDebtAbsorptionDefect N f =
      finitePartDebtAbsorptionWindow N f := by
  unfold finiteDiagonalDebtAbsorptionDefect
  unfold finitePositiveRenormalizedBoundaryWindow
  let Q : ℝ := finitePositiveSquareEnergyWindow N f
  let A : ℝ := finitePartDebtAbsorptionWindow N f
  have hcorrected :
      completedCorrectedBoundaryWindow N f = Q := by
    exact completedCorrectedBoundaryWindow_eq_finitePositiveSquareEnergyWindow N f
  change (completedCorrectedBoundaryWindow N f + A) - Q = A
  calc
    (completedCorrectedBoundaryWindow N f + A) - Q =
        (Q + A) - Q := by
      exact congrArg (fun x : ℝ => (x + A) - Q) hcorrected
    _ = (Q + A) + -Q := by
      exact sub_eq_add_neg (Q + A) Q
    _ = (A + Q) + -Q := by
      exact congrArg (fun x : ℝ => x + -Q) (add_comm Q A)
    _ = A + (Q + -Q) := by
      exact add_assoc A Q (-Q)
    _ = A + 0 := by
      exact congrArg (fun x : ℝ => A + x) (add_neg_cancel Q)
    _ = A := by
      exact add_zero A

/-- The completed corrected boundary window is nonnegative. -/
theorem completedCorrectedBoundaryWindow_nonnegative
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    0 ≤ completedCorrectedBoundaryWindow N f := by
  unfold completedCorrectedBoundaryWindow
  exact zetaCompletedPhysicalAutocorrelationBoundaryChannel_add_diagonalDebt_nonnegative N f

/-- Finite-part convergence to the completed physical finite-part boundary channel. This is the
genuine completed-normalization theorem before comparison with the explicit-formula boundary
functional. -/
theorem finitePartBoundaryWindow_tendsto_completedFinitePartBoundaryChannel
    (f : ZetaAdmissibleFunction) :
    Tendsto
      (fun N : ℕ => finitePartBoundaryWindow N f)
      atTop
      (𝓝 (completedFinitePartBoundaryChannel f)) := by
  let c : ℝ := completedFinitePartBoundaryChannel f
  have hrem :
      Tendsto (fun N : ℕ => finitePartBoundaryRemainder N f) atTop (𝓝 0) :=
    finitePartBoundaryRemainder_tendsto_zero f
  have hsum :
      Tendsto
        (fun N : ℕ => c + finitePartBoundaryRemainder N f)
        atTop
        (𝓝 (c + 0)) := by
    exact (tendsto_const_nhds.add hrem)
  have htarget : c + 0 = c := by
    exact add_zero c
  have hfinite :
      (fun N : ℕ => finitePartBoundaryWindow N f) =
      (fun N : ℕ => c + finitePartBoundaryRemainder N f) := by
    funext N
    exact finitePartBoundaryWindow_eq_boundaryChannel_add_remainder N f
  exact Eq.subst
    (motive := fun u : ℕ → ℝ => Tendsto u atTop (𝓝 c))
    hfinite.symm
    (Eq.subst
      (motive := fun x : ℝ =>
        Tendsto (fun N : ℕ => c + finitePartBoundaryRemainder N f) atTop (𝓝 x))
      htarget
      hsum)

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

/-- The completed physical finite-part channel is the real explicit-formula completed boundary
channel on the convolution-autocorrelation probe.  This is the owner bridge between the
renormalized square-energy completion and the explicit-formula boundary functional. -/
theorem completedFinitePartBoundaryChannel_eq_completedBoundaryChannel
    (f : ZetaAdmissibleFunction) :
    completedFinitePartBoundaryChannel f =
      Complex.re (completedBoundaryChannel (convolutionAutocorrelation f)) := by
  let g : ZetaAdmissibleFunction := convolutionAutocorrelation f
  have hprime :
      completedPrimeOffDiagonalChannel f =
        Complex.re (primeBoundaryChannel g) := by
    unfold g
    exact completedPrimeOffDiagonalChannel_eq_primeBoundaryChannel f
  have harch :
      zetaArchimedeanAutocorrelationSquareEnergy f =
        Complex.re (archimedeanBoundaryChannel g) := by
    unfold g
    unfold archimedeanBoundaryChannel
    exact (zetaArchimedeanAutocorrelationChannel_eq_squareEnergy f).symm
  have hcorr :
      zetaCorrectionAutocorrelationSquareEnergy f =
        Complex.re (poleBoundaryChannel g) := by
    unfold g
    unfold poleBoundaryChannel
    exact (zetaCorrectionAutocorrelationChannel_eq_squareEnergy f).symm
  have hcompletion :
      Complex.re (completionBoundaryChannel g) = 0 := by
    unfold g
    unfold completionBoundaryChannel
    exact Complex.zero_re
  have hboundary :
      Complex.re (completedBoundaryChannel g) =
        Complex.re (primeBoundaryChannel g) +
          Complex.re (archimedeanBoundaryChannel g) +
          Complex.re (poleBoundaryChannel g) +
          Complex.re (completionBoundaryChannel g) := by
    have hdecomp :
        completedBoundaryChannel g =
          primeBoundaryChannel g +
            archimedeanBoundaryChannel g +
            poleBoundaryChannel g +
            completionBoundaryChannel g :=
      completedBoundaryChannel_eq_prime_add_archimedean_add_pole_add_completion g
    calc
      Complex.re (completedBoundaryChannel g) =
          Complex.re
            (primeBoundaryChannel g +
              archimedeanBoundaryChannel g +
              poleBoundaryChannel g +
              completionBoundaryChannel g) := by
        exact congrArg Complex.re hdecomp
      _ =
          Complex.re
              (primeBoundaryChannel g +
                archimedeanBoundaryChannel g +
                poleBoundaryChannel g) +
            Complex.re (completionBoundaryChannel g) := by
        exact Complex.add_re
          (primeBoundaryChannel g +
            archimedeanBoundaryChannel g +
            poleBoundaryChannel g)
          (completionBoundaryChannel g)
      _ =
          (Complex.re (primeBoundaryChannel g + archimedeanBoundaryChannel g) +
              Complex.re (poleBoundaryChannel g)) +
            Complex.re (completionBoundaryChannel g) := by
        exact congrArg
          (fun x : ℝ => x + Complex.re (completionBoundaryChannel g))
          (Complex.add_re
            (primeBoundaryChannel g + archimedeanBoundaryChannel g)
            (poleBoundaryChannel g))
      _ =
          ((Complex.re (primeBoundaryChannel g) +
              Complex.re (archimedeanBoundaryChannel g)) +
            Complex.re (poleBoundaryChannel g)) +
            Complex.re (completionBoundaryChannel g) := by
        exact congrArg
          (fun x : ℝ =>
            (x + Complex.re (poleBoundaryChannel g)) +
              Complex.re (completionBoundaryChannel g))
          (Complex.add_re (primeBoundaryChannel g) (archimedeanBoundaryChannel g))
      _ =
          Complex.re (primeBoundaryChannel g) +
            Complex.re (archimedeanBoundaryChannel g) +
            Complex.re (poleBoundaryChannel g) +
            Complex.re (completionBoundaryChannel g) := by
        rfl
  unfold completedFinitePartBoundaryChannel
  calc
    completedPrimeOffDiagonalChannel f +
        zetaArchimedeanAutocorrelationSquareEnergy f +
        zetaCorrectionAutocorrelationSquareEnergy f =
        Complex.re (primeBoundaryChannel g) +
          Complex.re (archimedeanBoundaryChannel g) +
          Complex.re (poleBoundaryChannel g) := by
      exact congrArg₂ (fun x y : ℝ => x + y)
        (congrArg₂ (fun x y : ℝ => x + y) hprime harch)
        hcorr
    _ =
        Complex.re (primeBoundaryChannel g) +
          Complex.re (archimedeanBoundaryChannel g) +
          Complex.re (poleBoundaryChannel g) +
          0 := by
      exact (add_zero
        (Complex.re (primeBoundaryChannel g) +
          Complex.re (archimedeanBoundaryChannel g) +
          Complex.re (poleBoundaryChannel g))).symm
    _ =
        Complex.re (primeBoundaryChannel g) +
          Complex.re (archimedeanBoundaryChannel g) +
          Complex.re (poleBoundaryChannel g) +
          Complex.re (completionBoundaryChannel g) := by
      exact congrArg
        (fun x : ℝ =>
          Complex.re (primeBoundaryChannel g) +
            Complex.re (archimedeanBoundaryChannel g) +
            Complex.re (poleBoundaryChannel g) + x)
        hcompletion.symm
    _ = Complex.re (completedBoundaryChannel g) := by
      exact hboundary.symm

/-- Finite-part convergence to the completed boundary channel. This is the genuine completed
normalization theorem: diagonal debt cancellation has already happened inside
`finitePartBoundaryWindow`, so no separate convergence of the raw prime window is asserted. -/
theorem finitePartBoundaryWindow_tendsto_boundaryChannel
    (f : ZetaAdmissibleFunction) :
    Tendsto
      (fun N : ℕ => finitePartBoundaryWindow N f)
      atTop
      (𝓝 (Complex.re (completedBoundaryChannel (convolutionAutocorrelation f)))) := by
  have hfinite :
      Tendsto
        (fun N : ℕ => finitePartBoundaryWindow N f)
        atTop
        (𝓝 (completedFinitePartBoundaryChannel f)) :=
    finitePartBoundaryWindow_tendsto_completedFinitePartBoundaryChannel f
  exact Eq.subst
    (motive := fun x : ℝ =>
      Tendsto (fun N : ℕ => finitePartBoundaryWindow N f) atTop (𝓝 x))
    (completedFinitePartBoundaryChannel_eq_completedBoundaryChannel f)
    hfinite

/-- The finite positive square-energy windows, after finite diagonal-debt absorption, converge
to the completed boundary channel.  This is pure assembly: the absorption-renormalized positive
window is the finite-part window, and the finite-part window has the tail convergence
certificate above. -/
theorem finitePositiveRenormalizedBoundaryWindow_tendsto_boundaryChannel
    (f : ZetaAdmissibleFunction) :
    Tendsto
      (fun N : ℕ => finitePositiveRenormalizedBoundaryWindow N f)
      atTop
      (𝓝 (Complex.re (completedBoundaryChannel (convolutionAutocorrelation f)))) := by
  have hfinite :
      (fun N : ℕ => finitePositiveRenormalizedBoundaryWindow N f) =
        (fun N : ℕ => finitePartBoundaryWindow N f) := by
    funext N
    exact finitePositiveRenormalizedBoundaryWindow_eq_finitePartBoundaryWindow N f
  exact Eq.subst
    (motive := fun u : ℕ → ℝ =>
      Tendsto u atTop
        (𝓝 (Complex.re (completedBoundaryChannel (convolutionAutocorrelation f)))))
    hfinite.symm
    (finitePartBoundaryWindow_tendsto_boundaryChannel f)

/-- A completed boundary weight stream is a stream of finite weight objects together with the
real scalar realized by its finite-part representatives. -/
structure CompletedBoundaryWeightStream where
  source : ZetaAdmissibleFunction
  object : ℕ → FiniteBoundaryWeightObject
  scalar : ℝ
  scalar_eq_completedBoundaryChannel :
    scalar =
      Complex.re (completedBoundaryChannel (convolutionAutocorrelation source))
  finitePart_tendsto_scalar :
    Tendsto
      (fun N : ℕ =>
        FiniteBoundaryWeightObject.finitePartRepresentative (object N))
      atTop
      (𝓝 scalar)

namespace CompletedBoundaryWeightStream

/-- A completed boundary weight stream has pointwise nonnegative square representatives. -/
def SquareRepresentativesNonnegative
    (X : CompletedBoundaryWeightStream) : Prop :=
  ∀ N : ℕ, 0 ≤ FiniteBoundaryWeightObject.squareRepresentative (X.object N)

/-- A completed boundary weight stream has pointwise lower-weight absorption certificates. -/
def HasLowerWeightAbsorption
    (X : CompletedBoundaryWeightStream) : Prop :=
  ∀ N : ℕ, FiniteBoundaryLowerWeightAbsorptionCert (X.object N)

/-- The completed positive cone in the ordered heart: positivity means having square-positive
finite representatives together with lower-weight absorption certificates. -/
def InPositiveCone
    (X : CompletedBoundaryWeightStream) : Prop :=
  SquareRepresentativesNonnegative X ∧ HasLowerWeightAbsorption X

/-- Positive-cone membership supplies pointwise lower-weight exactness. -/
theorem lowerWeightExactRepresentative_eq_zero_of_inPositiveCone
    {X : CompletedBoundaryWeightStream}
    (hX : InPositiveCone X)
    (N : ℕ) :
    FiniteBoundaryWeightObject.lowerWeightExactRepresentative (X.object N) = 0 := by
  exact
    FiniteBoundaryLowerWeightAbsorptionCert.lowerWeightExactRepresentative_eq_zero
      (hX.2 N)

/-- Positive-cone membership supplies the pointwise weight-triangular transport identity. -/
theorem weightTriangularTransport_of_inPositiveCone
    {X : CompletedBoundaryWeightStream}
    (hX : InPositiveCone X)
    (N : ℕ) :
    FiniteBoundaryWeightObject.squareRepresentative (X.object N) +
        (X.object N).debtAbsorption =
      FiniteBoundaryWeightObject.finitePartRepresentative (X.object N) := by
  exact
    FiniteBoundaryLowerWeightAbsorptionCert.weightTriangularTransport
      (hX.2 N)

end CompletedBoundaryWeightStream

/-- The completed boundary weight stream attached to an admissible seed. -/
def completedBoundaryWeightStream
    (f : ZetaAdmissibleFunction) : CompletedBoundaryWeightStream :=
  { source := f
    object := fun N : ℕ => finiteBoundaryWeightObject N f
    scalar := Complex.re (completedBoundaryChannel (convolutionAutocorrelation f))
    scalar_eq_completedBoundaryChannel := rfl
    finitePart_tendsto_scalar := by
      have hfinite :
          Tendsto
            (fun N : ℕ => finitePartBoundaryWindow N f)
            atTop
            (𝓝 (Complex.re (completedBoundaryChannel (convolutionAutocorrelation f)))) :=
        finitePartBoundaryWindow_tendsto_boundaryChannel f
      have hobject :
          (fun N : ℕ =>
            FiniteBoundaryWeightObject.finitePartRepresentative
              (finiteBoundaryWeightObject N f)) =
            (fun N : ℕ => finitePartBoundaryWindow N f) := by
        funext N
        exact finiteBoundaryWeightObject_finitePartRepresentative_eq_finitePartBoundaryWindow
          N f
      exact Eq.subst
        (motive := fun u : ℕ → ℝ =>
          Tendsto u atTop
            (𝓝 (Complex.re (completedBoundaryChannel (convolutionAutocorrelation f)))))
        hobject.symm
        hfinite }

/-- The completed boundary weight stream has nonnegative square representatives. -/
theorem completedBoundaryWeightStream_squareRepresentatives_nonnegative
    (f : ZetaAdmissibleFunction) :
    CompletedBoundaryWeightStream.SquareRepresentativesNonnegative
      (completedBoundaryWeightStream f) := by
  intro N
  exact finiteBoundaryWeightObject_squareRepresentative_nonnegative N f

/-- The completed boundary weight stream has the pointwise lower-weight absorption
certificates. -/
theorem completedBoundaryWeightStream_hasLowerWeightAbsorption
    (f : ZetaAdmissibleFunction) :
    CompletedBoundaryWeightStream.HasLowerWeightAbsorption
      (completedBoundaryWeightStream f) := by
  intro N
  exact finiteBoundaryWeightObject_lowerWeightAbsorptionCert N f

/-- The completed boundary weight stream lies in the completed positive cone. -/
theorem completedBoundaryWeightStream_mem_positiveCone
    (f : ZetaAdmissibleFunction) :
    CompletedBoundaryWeightStream.InPositiveCone
      (completedBoundaryWeightStream f) := by
  exact
    ⟨completedBoundaryWeightStream_squareRepresentatives_nonnegative f,
      completedBoundaryWeightStream_hasLowerWeightAbsorption f⟩

/-- The concrete completed boundary weight stream has pointwise lower-weight exact
representatives. -/
theorem completedBoundaryWeightStream_lowerWeightExactRepresentative_eq_zero
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    FiniteBoundaryWeightObject.lowerWeightExactRepresentative
        ((completedBoundaryWeightStream f).object N) =
      0 := by
  exact
    CompletedBoundaryWeightStream.lowerWeightExactRepresentative_eq_zero_of_inPositiveCone
      (completedBoundaryWeightStream_mem_positiveCone f)
      N

/-- The concrete completed boundary weight stream satisfies weight-triangular transport
pointwise. -/
theorem completedBoundaryWeightStream_weightTriangularTransport
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    FiniteBoundaryWeightObject.squareRepresentative
        ((completedBoundaryWeightStream f).object N) +
      ((completedBoundaryWeightStream f).object N).debtAbsorption =
    FiniteBoundaryWeightObject.finitePartRepresentative
        ((completedBoundaryWeightStream f).object N) := by
  exact
    CompletedBoundaryWeightStream.weightTriangularTransport_of_inPositiveCone
      (completedBoundaryWeightStream_mem_positiveCone f)
      N

/-- The scalar of the completed boundary weight stream is the real completed boundary channel. -/
theorem completedBoundaryWeightStream_scalar_eq_boundaryChannel_re
    (f : ZetaAdmissibleFunction) :
    (completedBoundaryWeightStream f).scalar =
      Complex.re (completedBoundaryChannel (convolutionAutocorrelation f)) := by
  rfl

/-- The Hilbert-source object for the completed boundary realization.

The completed explicit-formula boundary channel is not a linear form on raw admissible
functions: the pole/correction contribution contains a fixed square coordinate.  The Hilbert
source therefore consists of the analytic seed together with that correction coordinate. -/
structure CompletedBoundaryHilbertSource where
  seed : ZetaAdmissibleFunction
  correctionCoordinate : ℝ

namespace CompletedBoundaryHilbertSource

instance : Zero CompletedBoundaryHilbertSource :=
  ⟨{ seed := 0
     correctionCoordinate := 0 }⟩

instance : Add CompletedBoundaryHilbertSource :=
  ⟨fun X Y =>
    { seed := X.seed + Y.seed
      correctionCoordinate := X.correctionCoordinate + Y.correctionCoordinate }⟩

instance : Neg CompletedBoundaryHilbertSource :=
  ⟨fun X =>
    { seed := -X.seed
      correctionCoordinate := -X.correctionCoordinate }⟩

instance : Sub CompletedBoundaryHilbertSource :=
  ⟨fun X Y => X + -Y⟩

instance : SMul ℝ CompletedBoundaryHilbertSource :=
  ⟨fun a X =>
    { seed := a • X.seed
      correctionCoordinate := a * X.correctionCoordinate }⟩

@[ext]
theorem ext
    {X Y : CompletedBoundaryHilbertSource}
    (hseed : X.seed = Y.seed)
    (hcorr : X.correctionCoordinate = Y.correctionCoordinate) :
    X = Y := by
  cases X with
  | mk Xseed Xcorr =>
    cases Y with
    | mk Yseed Ycorr =>
      change Xseed = Yseed at hseed
      change Xcorr = Ycorr at hcorr
      cases hseed
      cases hcorr
      rfl

instance : AddCommGroup CompletedBoundaryHilbertSource where
  zero := 0
  add := (· + ·)
  neg := Neg.neg
  sub := Sub.sub
  zsmul := fun n X =>
    { seed := n • X.seed
      correctionCoordinate := n * X.correctionCoordinate }
  add_assoc := by
    intro X Y Z
    ext
    · exact add_assoc X.seed Y.seed Z.seed
    · exact add_assoc X.correctionCoordinate Y.correctionCoordinate Z.correctionCoordinate
  zero_add := by
    intro X
    ext
    · exact zero_add X.seed
    · exact zero_add X.correctionCoordinate
  add_zero := by
    intro X
    ext
    · exact add_zero X.seed
    · exact add_zero X.correctionCoordinate
  add_comm := by
    intro X Y
    ext
    · exact add_comm X.seed Y.seed
    · exact add_comm X.correctionCoordinate Y.correctionCoordinate
  add_left_neg := by
    intro X
    ext
    · exact neg_add_cancel X.seed
    · exact neg_add_cancel X.correctionCoordinate
  sub_eq_add_neg := by
    intro X Y
    rfl
  nsmul := fun n X =>
    { seed := n • X.seed
      correctionCoordinate := n * X.correctionCoordinate }
  nsmul_zero := by
    intro X
    ext
    · exact nsmul_zero X.seed
    · change ((0 : ℕ) : ℝ) * X.correctionCoordinate = 0
      exact zero_mul X.correctionCoordinate
  nsmul_succ := by
    intro n X
    ext
    · exact nsmul_succ n X.seed
    · change ((n + 1 : ℕ) : ℝ) * X.correctionCoordinate =
        n * X.correctionCoordinate + X.correctionCoordinate
      calc
        ((n + 1 : ℕ) : ℝ) * X.correctionCoordinate =
            (((n : ℕ) : ℝ) + 1) * X.correctionCoordinate := by
          exact congrArg (fun a : ℝ => a * X.correctionCoordinate)
            (Nat.cast_add n 1)
        _ =
            ((n : ℕ) : ℝ) * X.correctionCoordinate +
              1 * X.correctionCoordinate := by
          exact add_mul ((n : ℕ) : ℝ) 1 X.correctionCoordinate
        _ =
            ((n : ℕ) : ℝ) * X.correctionCoordinate +
              X.correctionCoordinate := by
          exact congrArg
            (fun a : ℝ => ((n : ℕ) : ℝ) * X.correctionCoordinate + a)
            (one_mul X.correctionCoordinate)
  zsmul_zero' := by
    intro X
    ext
    · exact zsmul_zero' X.seed
    · change ((0 : ℤ) : ℝ) * X.correctionCoordinate = 0
      exact zero_mul X.correctionCoordinate
  zsmul_succ' := by
    intro n X
    ext
    · exact zsmul_succ' n X.seed
    · change (((Int.ofNat n + 1 : ℤ) : ℝ) * X.correctionCoordinate) =
        (n : ℤ) * X.correctionCoordinate + X.correctionCoordinate
      have hcast :
          ((Int.ofNat n + 1 : ℤ) : ℝ) = ((n : ℤ) : ℝ) + 1 := by
        exact Int.cast_add (Int.ofNat n) 1
      calc
        ((Int.ofNat n + 1 : ℤ) : ℝ) * X.correctionCoordinate =
            (((n : ℤ) : ℝ) + 1) * X.correctionCoordinate := by
          exact congrArg (fun a : ℝ => a * X.correctionCoordinate) hcast
        _ =
            ((n : ℤ) : ℝ) * X.correctionCoordinate +
              1 * X.correctionCoordinate := by
          exact add_mul ((n : ℤ) : ℝ) 1 X.correctionCoordinate
        _ =
            ((n : ℤ) : ℝ) * X.correctionCoordinate +
              X.correctionCoordinate := by
          exact congrArg
            (fun a : ℝ => ((n : ℤ) : ℝ) * X.correctionCoordinate + a)
            (one_mul X.correctionCoordinate)
  zsmul_neg' := by
    intro n X
    ext
    · exact zsmul_neg' n X.seed
    · change (((-Int.ofNat n : ℤ) : ℝ) * X.correctionCoordinate) =
        -(((n : ℤ) : ℝ) * X.correctionCoordinate)
      calc
        ((-Int.ofNat n : ℤ) : ℝ) * X.correctionCoordinate =
            (-((n : ℤ) : ℝ)) * X.correctionCoordinate := by
          exact congrArg (fun a : ℝ => a * X.correctionCoordinate)
            (Int.cast_neg (Int.ofNat n))
        _ = -(((n : ℤ) : ℝ) * X.correctionCoordinate) := by
          exact neg_mul ((n : ℤ) : ℝ) X.correctionCoordinate

instance : Module ℝ CompletedBoundaryHilbertSource where
  one_smul := by
    intro X
    ext
    · exact one_smul ℝ X.seed
    · exact one_mul X.correctionCoordinate
  mul_smul := by
    intro a b X
    ext
    · exact mul_smul a b X.seed
    · exact mul_assoc a b X.correctionCoordinate
  smul_zero := by
    intro a
    ext
    · exact smul_zero a
    · exact mul_zero a
  smul_add := by
    intro a X Y
    ext
    · exact smul_add a X.seed Y.seed
    · exact mul_add a X.correctionCoordinate Y.correctionCoordinate
  add_smul := by
    intro a b X
    ext
    · exact add_smul a b X.seed
    · exact add_mul a b X.correctionCoordinate
  zero_smul := by
    intro X
    ext
    · exact zero_smul ℝ X.seed
    · exact zero_mul X.correctionCoordinate

end CompletedBoundaryHilbertSource

/-- The completed Hilbert source attached to an admissible seed.  The correction coordinate is
the explicit square-root correction packet coordinate. -/
def completedBoundaryHilbertSource
    (f : ZetaAdmissibleFunction) : CompletedBoundaryHilbertSource :=
  { seed := f
    correctionCoordinate := zetaCompletionCorrectionPacketCoordinate }

/-- The packet realization of a completed Hilbert source.

The correction coordinate is the source coordinate, not the fixed completed-zeta coordinate.
This keeps the packet realization compatible with lower-weight source changes and makes the
GNS scalar a genuine packet-kernel scalar. -/
noncomputable def completedBoundaryHilbertSourcePacket
    (X : CompletedBoundaryHilbertSource) : ZetaPacketEnsemble :=
  zetaCompletedBoundaryDefectPrime X.seed +
    zetaCompletedBoundaryDefectArchimedean X.seed +
    ZetaPacketEnsemble.single ZetaPacketLabel.correction X.correctionCoordinate

/-- The completed real-shadow packet kernel on Hilbert sources, realized as the packet dot
product.  This kernel remains available for packet-comparison statements; the ordered-heart
scalar below is owned by the Hermitian defect-kernel realization. -/
noncomputable def completedBoundaryGNSKernel
    (X Y : CompletedBoundaryHilbertSource) : ℝ :=
  ZetaPacketEnsemble.dotProduct
    (completedBoundaryHilbertSourcePacket X)
    (completedBoundaryHilbertSourcePacket Y)

/-- The completed positive GNS kernel is symmetric. -/
theorem completedBoundaryGNSKernel_symmetric
    (X Y : CompletedBoundaryHilbertSource) :
    completedBoundaryGNSKernel X Y =
      completedBoundaryGNSKernel Y X := by
  unfold completedBoundaryGNSKernel
  exact ZetaPacketEnsemble.dotProduct_comm
    (completedBoundaryHilbertSourcePacket X)
    (completedBoundaryHilbertSourcePacket Y)

/-- The completed positive GNS radical is the zero-norm radical of the packet kernel. -/
def completedBoundaryGNSRadical
    (X : CompletedBoundaryHilbertSource) : Prop :=
  completedBoundaryGNSKernel X X = 0

/-- Zero GNS norm kills left cross-terms in the completed positive packet kernel. -/
theorem completedBoundaryGNSKernel_left_zero_of_self_zero
    {X Y : CompletedBoundaryHilbertSource}
    (hX : completedBoundaryGNSRadical X) :
    completedBoundaryGNSKernel X Y = 0 := by
  unfold completedBoundaryGNSRadical at hX
  unfold completedBoundaryGNSKernel at hX
  unfold completedBoundaryGNSKernel
  exact ZetaPacketEnsemble.dotProduct_left_eq_zero_of_normSq_eq_zero hX

/-- Zero GNS norm kills right cross-terms in the completed positive packet kernel. -/
theorem completedBoundaryGNSKernel_right_zero_of_self_zero
    {X Y : CompletedBoundaryHilbertSource}
    (hY : completedBoundaryGNSRadical Y) :
    completedBoundaryGNSKernel X Y = 0 := by
  unfold completedBoundaryGNSRadical at hY
  unfold completedBoundaryGNSKernel at hY
  unfold completedBoundaryGNSKernel
  exact ZetaPacketEnsemble.dotProduct_right_eq_zero_of_normSq_eq_zero hY

/-- The completed positive GNS kernel is nonnegative on the diagonal. -/
theorem completedBoundaryGNSKernel_self_nonnegative
    (X : CompletedBoundaryHilbertSource) :
    0 ≤ completedBoundaryGNSKernel X X := by
  unfold completedBoundaryGNSKernel
  exact ZetaPacketEnsemble.normSq_nonneg
    (completedBoundaryHilbertSourcePacket X)

/-- The real-shadow packet norm-square of the canonical Hilbert source.  This is a packet
comparison scalar, not the owner scalar of the completed ordered heart. -/
def completedBoundaryRealShadowGNSNormSq
    (f : ZetaAdmissibleFunction) : ℝ :=
  completedBoundaryGNSKernel
    (completedBoundaryHilbertSource f)
    (completedBoundaryHilbertSource f)

/-- The real-shadow packet norm-square is nonnegative. -/
theorem completedBoundaryRealShadowGNSNormSq_nonnegative
    (f : ZetaAdmissibleFunction) :
    0 ≤ completedBoundaryRealShadowGNSNormSq f := by
  unfold completedBoundaryRealShadowGNSNormSq
  exact completedBoundaryGNSKernel_self_nonnegative
    (completedBoundaryHilbertSource f)

/-- The Hermitian defect-kernel scalar attached to a completed Hilbert source.  The prime
part is the positive defect-square kernel; the archimedean part is the Hermitian packet
Gram; the correction coordinate is owned by the source itself. -/
noncomputable def completedBoundaryHermitianGNSScalar
    (X : CompletedBoundaryHilbertSource) : ℝ :=
  Complex.re (zetaPrimeDefectKernelPositiveForm X.seed) +
    ZetaHermitianPacketEnsemble.archimedeanPacketGram
      (zetaCompletedHermitianBoundaryDefect X.seed) +
    X.correctionCoordinate * X.correctionCoordinate

/-- The Hermitian defect-kernel scalar is nonnegative on every completed Hilbert source. -/
theorem completedBoundaryHermitianGNSScalar_nonnegative
    (X : CompletedBoundaryHilbertSource) :
    0 ≤ completedBoundaryHermitianGNSScalar X := by
  have hprime :
      0 ≤ Complex.re (zetaPrimeDefectKernelPositiveForm X.seed) :=
    zetaPrimeDefectKernelPositiveForm_re_nonnegative X.seed
  have harch :
      0 ≤ ZetaHermitianPacketEnsemble.archimedeanPacketGram
          (zetaCompletedHermitianBoundaryDefect X.seed) :=
    ZetaHermitianPacketEnsemble.archimedeanPacketGram_nonnegative
      (zetaCompletedHermitianBoundaryDefect X.seed)
  have hcorr : 0 ≤ X.correctionCoordinate * X.correctionCoordinate :=
    mul_self_nonneg X.correctionCoordinate
  unfold completedBoundaryHermitianGNSScalar
  exact add_nonneg (add_nonneg hprime harch) hcorr

/-- On canonical sources, the Hermitian defect-kernel scalar is the positive completed GNS
boundary scalar. -/
theorem completedBoundaryHermitianGNSScalar_source_eq_positiveBoundaryScalar
    (f : ZetaAdmissibleFunction) :
    completedBoundaryHermitianGNSScalar (completedBoundaryHilbertSource f) =
      Complex.re (zetaCompletedGNSPositiveBoundaryForm f) := by
  unfold completedBoundaryHermitianGNSScalar
  unfold completedBoundaryHilbertSource
  unfold zetaCompletedGNSPositiveBoundaryForm
  have hcorr :
      zetaCompletionCorrectionPacketCoordinate *
          zetaCompletionCorrectionPacketCoordinate =
        ZetaHermitianPacketEnsemble.correctionPacketGram
          (zetaCompletedHermitianBoundaryDefect f) := by
    exact
      (zetaCompletedHermitianBoundaryDefect_correctionPacketGram_eq_coordinate_sq
        f).symm
  calc
    Complex.re (zetaPrimeDefectKernelPositiveForm f) +
        ZetaHermitianPacketEnsemble.archimedeanPacketGram
          (zetaCompletedHermitianBoundaryDefect f) +
        zetaCompletionCorrectionPacketCoordinate *
          zetaCompletionCorrectionPacketCoordinate =
        Complex.re (zetaPrimeDefectKernelPositiveForm f) +
          ZetaHermitianPacketEnsemble.archimedeanPacketGram
            (zetaCompletedHermitianBoundaryDefect f) +
          ZetaHermitianPacketEnsemble.correctionPacketGram
            (zetaCompletedHermitianBoundaryDefect f) := by
      exact congrArg
        (fun x : ℝ =>
          Complex.re (zetaPrimeDefectKernelPositiveForm f) +
            ZetaHermitianPacketEnsemble.archimedeanPacketGram
              (zetaCompletedHermitianBoundaryDefect f) +
            x)
        hcorr
    _ =
        Complex.re
          (zetaPrimeDefectKernelPositiveForm f +
            (ZetaHermitianPacketEnsemble.archimedeanPacketGram
              (zetaCompletedHermitianBoundaryDefect f) : ℂ) +
            (ZetaHermitianPacketEnsemble.correctionPacketGram
              (zetaCompletedHermitianBoundaryDefect f) : ℂ)) := by
      let P : ℂ := zetaPrimeDefectKernelPositiveForm f
      let A : ℝ :=
        ZetaHermitianPacketEnsemble.archimedeanPacketGram
          (zetaCompletedHermitianBoundaryDefect f)
      let C : ℝ :=
        ZetaHermitianPacketEnsemble.correctionPacketGram
          (zetaCompletedHermitianBoundaryDefect f)
      change Complex.re P + A + C = Complex.re (P + (A : ℂ) + (C : ℂ))
      calc
        Complex.re P + A + C =
            (Complex.re P + Complex.re (A : ℂ)) + Complex.re (C : ℂ) := by
          exact congrArg₂ HAdd.hAdd
            (congrArg₂ HAdd.hAdd rfl (Complex.ofReal_re A).symm)
            (Complex.ofReal_re C).symm
        _ = Complex.re (P + (A : ℂ)) + Complex.re (C : ℂ) := by
          exact congrArg
            (fun x : ℝ => x + Complex.re (C : ℂ))
            (Complex.add_re P (A : ℂ)).symm
        _ = Complex.re (P + (A : ℂ) + (C : ℂ)) := by
          exact (Complex.add_re (P + (A : ℂ)) (C : ℂ)).symm

/-- The lower-weight exact Hilbert source is the zero source: it has no analytic seed and no
correction square coordinate. -/
def completedBoundaryLowerWeightExactHilbertSource :
    CompletedBoundaryHilbertSource :=
  0

/-- The reduced completed boundary channel: prime, archimedean, and residual completion
channels, with the affine pole/correction square coordinate removed from the raw boundary
functional. -/
def completedBoundaryReducedChannel
    (g : ZetaAdmissibleFunction) : ℂ :=
  primeBoundaryChannel g +
    archimedeanBoundaryChannel g +
    completionBoundaryChannel g

/-- The completed Hilbert pairing.  The reduced analytic channel is paired through
`convolutionPair`; the correction contribution is paired by the explicit real correction
coordinate. -/
def completedBoundaryHilbertPairing
    (X Y : CompletedBoundaryHilbertSource) : ℝ :=
  Complex.re
      (completedBoundaryReducedChannel (convolutionPair X.seed Y.seed)) +
    X.correctionCoordinate * Y.correctionCoordinate

/-- A Hilbert source is lower-weight radical when it pairs trivially with every completed
Hilbert source on both sides. -/
def CompletedBoundaryHilbertSource.LowerWeightRadical
    (D : CompletedBoundaryHilbertSource) : Prop :=
  ∀ T : CompletedBoundaryHilbertSource,
    completedBoundaryHilbertPairing D T = 0 ∧
      completedBoundaryHilbertPairing T D = 0

/-- The scalar induced by the completed positive GNS kernel on a Hilbert-source representative
of the ordered heart. -/
def completedOrderedHeartScalar
    (X : CompletedBoundaryHilbertSource) : ℝ :=
  completedBoundaryHermitianGNSScalar X

/-- Two completed Hilbert sources are GNS-tomographically equivalent when they have the same
Hermitian defect-kernel scalar in the completed ordered heart. -/
def CompletedBoundaryHilbertSource.GNSTomographicallyEquivalent
    (X Y : CompletedBoundaryHilbertSource) : Prop :=
  completedBoundaryHermitianGNSScalar X =
    completedBoundaryHermitianGNSScalar Y

/-- GNS-tomographic equivalence is reflexive. -/
theorem CompletedBoundaryHilbertSource.GNSTomographicallyEquivalent.refl
    (X : CompletedBoundaryHilbertSource) :
    CompletedBoundaryHilbertSource.GNSTomographicallyEquivalent X X := by
  rfl

/-- GNS-tomographic equivalence is symmetric. -/
theorem CompletedBoundaryHilbertSource.GNSTomographicallyEquivalent.symm
    {X Y : CompletedBoundaryHilbertSource}
    (h :
      CompletedBoundaryHilbertSource.GNSTomographicallyEquivalent X Y) :
    CompletedBoundaryHilbertSource.GNSTomographicallyEquivalent Y X := by
  exact h.symm

/-- GNS-tomographic equivalence is transitive. -/
theorem CompletedBoundaryHilbertSource.GNSTomographicallyEquivalent.trans
    {X Y Z : CompletedBoundaryHilbertSource}
    (hXY :
      CompletedBoundaryHilbertSource.GNSTomographicallyEquivalent X Y)
    (hYZ :
      CompletedBoundaryHilbertSource.GNSTomographicallyEquivalent Y Z) :
    CompletedBoundaryHilbertSource.GNSTomographicallyEquivalent X Z := by
  exact hXY.trans hYZ

/-- GNS tomography determines the ordered-heart scalar.  This is the positive-kernel
analogue of projective tomography: equality against all probes identifies the diagonal
quadratic scalar in the completed ordered heart. -/
theorem completedOrderedHeartScalar_eq_of_GNSTomography
    {X Y : CompletedBoundaryHilbertSource}
    (h :
      CompletedBoundaryHilbertSource.GNSTomographicallyEquivalent X Y) :
    completedOrderedHeartScalar X = completedOrderedHeartScalar Y := by
  unfold completedOrderedHeartScalar
  exact h

/-- Equal Hilbert-source representatives are GNS-tomographically equivalent. -/
theorem completedBoundaryHilbertSource_GNSTomography_of_eq
    {X Y : CompletedBoundaryHilbertSource}
    (hXY : X = Y) :
    CompletedBoundaryHilbertSource.GNSTomographicallyEquivalent X Y := by
  exact Eq.subst
    (motive := fun Z : CompletedBoundaryHilbertSource =>
      CompletedBoundaryHilbertSource.GNSTomographicallyEquivalent X Z)
    hXY.symm
    (CompletedBoundaryHilbertSource.GNSTomographicallyEquivalent.refl X)

/-- Equal Hilbert-source representatives have the same ordered-heart scalar. -/
theorem completedOrderedHeartScalar_eq_of_eq
    {X Y : CompletedBoundaryHilbertSource}
    (hXY : X = Y) :
    completedOrderedHeartScalar X = completedOrderedHeartScalar Y :=
  completedOrderedHeartScalar_eq_of_GNSTomography
    (completedBoundaryHilbertSource_GNSTomography_of_eq hXY)

/-- The completed ordered-heart quotient relation on Hilbert-source representatives. -/
def completedBoundaryHilbertSourceGNSTomographySetoid :
    Setoid CompletedBoundaryHilbertSource where
  r := CompletedBoundaryHilbertSource.GNSTomographicallyEquivalent
  iseqv := by
    constructor
    · intro X
      exact CompletedBoundaryHilbertSource.GNSTomographicallyEquivalent.refl X
    · intro X Y hXY
      exact CompletedBoundaryHilbertSource.GNSTomographicallyEquivalent.symm hXY
    · intro X Y Z hXY hYZ
      exact CompletedBoundaryHilbertSource.GNSTomographicallyEquivalent.trans hXY hYZ

/-- The completed ordered heart: Hilbert sources modulo lower-weight/GNS tomography. -/
abbrev CompletedBoundaryOrderedHeartClass :=
  Quotient completedBoundaryHilbertSourceGNSTomographySetoid

/-- The quotient class of a completed Hilbert-source representative. -/
def completedBoundaryOrderedHeartClass
    (X : CompletedBoundaryHilbertSource) :
    CompletedBoundaryOrderedHeartClass :=
  Quotient.mk completedBoundaryHilbertSourceGNSTomographySetoid X

/-- The ordered-heart scalar descends through GNS-tomographic equivalence. -/
def completedBoundaryOrderedHeartClassScalar :
    CompletedBoundaryOrderedHeartClass → ℝ :=
  Quotient.lift completedOrderedHeartScalar
    (fun X Y hXY => completedOrderedHeartScalar_eq_of_GNSTomography hXY)

/-- The scalar of a represented ordered-heart class is the representative's ordered-heart
scalar. -/
theorem completedBoundaryOrderedHeartClassScalar_mk
    (X : CompletedBoundaryHilbertSource) :
    completedBoundaryOrderedHeartClassScalar
        (completedBoundaryOrderedHeartClass X) =
      completedOrderedHeartScalar X := by
  rfl

/-- GNS-tomographically equivalent representatives define the same completed ordered-heart
class. -/
theorem completedBoundaryOrderedHeartClass_eq_of_GNSTomography
    {X Y : CompletedBoundaryHilbertSource}
    (hXY :
      CompletedBoundaryHilbertSource.GNSTomographicallyEquivalent X Y) :
    completedBoundaryOrderedHeartClass X =
      completedBoundaryOrderedHeartClass Y := by
  exact Quotient.sound hXY

/-- Equal Hilbert-source representatives define the same completed ordered-heart class. -/
theorem completedBoundaryOrderedHeartClass_eq_of_eq
    {X Y : CompletedBoundaryHilbertSource}
    (hXY : X = Y) :
    completedBoundaryOrderedHeartClass X =
      completedBoundaryOrderedHeartClass Y := by
  exact completedBoundaryOrderedHeartClass_eq_of_GNSTomography
    (completedBoundaryHilbertSource_GNSTomography_of_eq hXY)

/-- The completed GNS norm-square induced by the completed Hilbert quotient pairing.

This is the canonical ordered-heart scalar of the realized Hilbert source, owned by the
positive packet kernel.  The reduced time-side boundary pairing is related to this scalar by
separate transport/comparison theorems. -/
def completedBoundaryGNSNormSq
    (f : ZetaAdmissibleFunction) : ℝ :=
  completedOrderedHeartScalar (completedBoundaryHilbertSource f)

/-- The completed GNS norm-square is the ordered-heart scalar of the realized Hilbert source. -/
theorem completedBoundaryGNSNormSq_eq_orderedHeartScalar
    (f : ZetaAdmissibleFunction) :
    completedBoundaryGNSNormSq f =
      completedOrderedHeartScalar (completedBoundaryHilbertSource f) := by
  rfl

/-- The completed GNS norm-square is induced by the Hermitian defect-kernel ordered-heart
scalar. -/
theorem completedBoundaryGNSNormSq_eq_hermitianGNSScalar
    (f : ZetaAdmissibleFunction) :
    completedBoundaryGNSNormSq f =
      completedBoundaryHermitianGNSScalar
        (completedBoundaryHilbertSource f) := by
  rfl

/-- The completed ordered-heart GNS norm-square is nonnegative. -/
theorem completedBoundaryGNSNormSq_nonnegative
    (f : ZetaAdmissibleFunction) :
    0 ≤ completedBoundaryGNSNormSq f := by
  unfold completedBoundaryGNSNormSq
  unfold completedOrderedHeartScalar
  exact completedBoundaryHermitianGNSScalar_nonnegative
    (completedBoundaryHilbertSource f)

/-- The completed renormalized defect-kernel channel is the ordered-heart GNS norm-square.
This is the owner-level payoff of the weight-triangular realization: after finite
diagonal-debt absorption, the completed channel is represented by the positive Hermitian
defect kernel. -/
theorem completedRenormalizedDefectKernelBoundaryChannel_eq_GNSNormSq
    (f : ZetaAdmissibleFunction) :
    completedRenormalizedDefectKernelBoundaryChannel f =
      completedBoundaryGNSNormSq f := by
  unfold completedRenormalizedDefectKernelBoundaryChannel
  unfold completedPrimeDefectKernelPositiveChannel
  unfold completedBoundaryGNSNormSq
  unfold completedOrderedHeartScalar
  unfold completedBoundaryHermitianGNSScalar
  unfold completedBoundaryHilbertSource
  have hcorr :
      ZetaHermitianPacketEnsemble.correctionPacketGram
          (zetaCompletedHermitianBoundaryDefect f) =
        zetaCompletionCorrectionPacketCoordinate *
          zetaCompletionCorrectionPacketCoordinate :=
    zetaCompletedHermitianBoundaryDefect_correctionPacketGram_eq_coordinate_sq f
  exact congrArg
    (fun x : ℝ =>
      Complex.re (zetaPrimeDefectKernelPositiveForm f) +
        ZetaHermitianPacketEnsemble.archimedeanPacketGram
          (zetaCompletedHermitianBoundaryDefect f) +
        x)
    hcorr

/-- Compatibility name for the completed positive GNS norm-square.  The owner scalar is
`completedBoundaryGNSNormSq`; this abbreviation keeps older packet-comparison wrappers useful
without creating a second scalar. -/
abbrev completedBoundaryGNSPositiveNormSq
    (f : ZetaAdmissibleFunction) : ℝ :=
  completedBoundaryGNSNormSq f

/-- The completed positive GNS norm-square is nonnegative. -/
theorem completedBoundaryGNSPositiveNormSq_nonnegative
    (f : ZetaAdmissibleFunction) :
    0 ≤ completedBoundaryGNSPositiveNormSq f := by
  exact completedBoundaryGNSNormSq_nonnegative f

/-- The Hilbert pairing unfolds to the reduced analytic source pairing plus the explicit
correction-coordinate product. -/
theorem completedBoundaryHilbertPairing_eq_reduced_add_correction
    (X Y : CompletedBoundaryHilbertSource) :
    completedBoundaryHilbertPairing X Y =
      Complex.re
          (completedBoundaryReducedChannel (convolutionPair X.seed Y.seed)) +
        X.correctionCoordinate * Y.correctionCoordinate := by
  rfl

/-- The scalar induced by the reduced time-side Hilbert pairing.  This is retained as a
comparison scalar; the completed ordered-heart scalar is owned by the positive GNS kernel. -/
def completedBoundaryTimePairingScalar
    (X : CompletedBoundaryHilbertSource) : ℝ :=
  completedBoundaryHilbertPairing X X

/-- The prime boundary channel vanishes on the zero admissible probe. -/
theorem primeBoundaryChannel_zero :
    primeBoundaryChannel (0 : ZetaAdmissibleFunction) = 0 := by
  unfold primeBoundaryChannel
  unfold zetaCompletedExplicitFormulaPrimeContribution
  unfold zetaCompletedExplicitFormulaPrimePowerContribution
  let term : ZetaPrimePowerIndex → ℝ :=
    fun ι : ZetaPrimePowerIndex =>
      -(ZetaPrimePowerIndex.weight ι *
        Complex.re
          (zetaCompletedTimeBoundaryValue (0 : ZetaAdmissibleFunction)
              (ZetaPrimePowerIndex.center ι) +
            star
              (zetaCompletedTimeBoundaryValue (0 : ZetaAdmissibleFunction)
                (ZetaPrimePowerIndex.center ι))))
  have hterm : term = fun _ι : ZetaPrimePowerIndex => 0 := by
    funext ι
    unfold term
    have hpos :
        zetaCompletedTimeBoundaryValue (0 : ZetaAdmissibleFunction)
            (ZetaPrimePowerIndex.center ι) =
          0 :=
      zetaCompletedTimeBoundaryValue_zero (ZetaPrimePowerIndex.center ι)
    have hstar :
        star
            (zetaCompletedTimeBoundaryValue (0 : ZetaAdmissibleFunction)
              (ZetaPrimePowerIndex.center ι)) =
          0 := by
      exact (congrArg star hpos).trans (star_zero ℂ)
    have hsum :
        zetaCompletedTimeBoundaryValue (0 : ZetaAdmissibleFunction)
            (ZetaPrimePowerIndex.center ι) +
          star
            (zetaCompletedTimeBoundaryValue (0 : ZetaAdmissibleFunction)
              (ZetaPrimePowerIndex.center ι)) =
        0 := by
      calc
        zetaCompletedTimeBoundaryValue (0 : ZetaAdmissibleFunction)
            (ZetaPrimePowerIndex.center ι) +
          star
            (zetaCompletedTimeBoundaryValue (0 : ZetaAdmissibleFunction)
              (ZetaPrimePowerIndex.center ι)) =
            0 + 0 := by
          exact congrArg₂ HAdd.hAdd hpos hstar
        _ = 0 := by
          exact zero_add 0
    have hre :
        Complex.re
          (zetaCompletedTimeBoundaryValue (0 : ZetaAdmissibleFunction)
              (ZetaPrimePowerIndex.center ι) +
            star
              (zetaCompletedTimeBoundaryValue (0 : ZetaAdmissibleFunction)
                (ZetaPrimePowerIndex.center ι))) =
          0 := by
      exact (congrArg Complex.re hsum).trans Complex.zero_re
    calc
      -(ZetaPrimePowerIndex.weight ι *
          Complex.re
            (zetaCompletedTimeBoundaryValue (0 : ZetaAdmissibleFunction)
                (ZetaPrimePowerIndex.center ι) +
              star
                (zetaCompletedTimeBoundaryValue (0 : ZetaAdmissibleFunction)
                  (ZetaPrimePowerIndex.center ι)))) =
          -(ZetaPrimePowerIndex.weight ι * 0) := by
        exact congrArg
          (fun x : ℝ => -(ZetaPrimePowerIndex.weight ι * x))
          hre
      _ = -0 := by
        exact congrArg Neg.neg (mul_zero (ZetaPrimePowerIndex.weight ι))
      _ = 0 := by
        exact neg_zero
  change ((∑' ι : ZetaPrimePowerIndex, term ι) : ℂ) = 0
  calc
    ((∑' ι : ZetaPrimePowerIndex, term ι) : ℂ) =
        ((∑' _ι : ZetaPrimePowerIndex, (0 : ℝ)) : ℂ) := by
      exact congrArg
        (fun u : ZetaPrimePowerIndex → ℝ =>
          ((∑' ι : ZetaPrimePowerIndex, u ι) : ℂ))
        hterm
    _ = ((0 : ℝ) : ℂ) := by
      exact congrArg (fun x : ℝ => (x : ℂ)) (tsum_zero)
    _ = 0 := by
      exact Complex.ofReal_zero

/-- The archimedean boundary channel vanishes on the zero admissible probe. -/
theorem archimedeanBoundaryChannel_zero :
    archimedeanBoundaryChannel (0 : ZetaAdmissibleFunction) = 0 := by
  unfold archimedeanBoundaryChannel
  unfold zetaCompletedExplicitFormulaArchimedeanContribution
  have hphi :
      zetaCompletedExplicitFormulaPhi (0 : ZetaAdmissibleFunction) 0 = 0 :=
    zetaCompletedExplicitFormulaPhi_zero 0
  calc
    (2 : ℂ) * zetaCompletedExplicitFormulaPhi (0 : ZetaAdmissibleFunction) 0 =
        (2 : ℂ) * 0 := by
      exact congrArg (fun z : ℂ => (2 : ℂ) * z) hphi
    _ = 0 := by
      exact mul_zero (2 : ℂ)

/-- The residual completion boundary channel vanishes on the zero admissible probe. -/
theorem completionBoundaryChannel_zero :
    completionBoundaryChannel (0 : ZetaAdmissibleFunction) = 0 := by
  rfl

/-- The reduced completed boundary channel vanishes on the zero admissible probe. -/
theorem completedBoundaryReducedChannel_zero :
    completedBoundaryReducedChannel (0 : ZetaAdmissibleFunction) = 0 := by
  unfold completedBoundaryReducedChannel
  calc
    primeBoundaryChannel (0 : ZetaAdmissibleFunction) +
        archimedeanBoundaryChannel (0 : ZetaAdmissibleFunction) +
        completionBoundaryChannel (0 : ZetaAdmissibleFunction) =
      0 + 0 + 0 := by
      exact congrArg₂ HAdd.hAdd
        (congrArg₂ HAdd.hAdd primeBoundaryChannel_zero archimedeanBoundaryChannel_zero)
        completionBoundaryChannel_zero
    _ = 0 + 0 := by
      exact add_zero (0 + 0)
    _ = 0 := by
      exact zero_add 0

/-- The reduced completed boundary channel of the zero convolution pair is zero. -/
theorem completedBoundaryReducedChannel_convolutionPair_zero_zero :
    completedBoundaryReducedChannel
        (convolutionPair (0 : ZetaAdmissibleFunction) 0) =
      0 := by
  exact (congrArg completedBoundaryReducedChannel convolutionPair_zero_zero).trans
    completedBoundaryReducedChannel_zero

/-- The reduced completed boundary channel of a convolution pair with zero left input is
zero. -/
theorem completedBoundaryReducedChannel_convolutionPair_zero_left
    (h : ZetaAdmissibleFunction) :
    completedBoundaryReducedChannel
        (convolutionPair (0 : ZetaAdmissibleFunction) h) =
      0 := by
  exact (congrArg completedBoundaryReducedChannel (convolutionPair_zero_left h)).trans
    completedBoundaryReducedChannel_zero

/-- The reduced completed boundary channel of a convolution pair with zero right input is
zero. -/
theorem completedBoundaryReducedChannel_convolutionPair_zero_right
    (f : ZetaAdmissibleFunction) :
    completedBoundaryReducedChannel
        (convolutionPair f (0 : ZetaAdmissibleFunction)) =
      0 := by
  exact (congrArg completedBoundaryReducedChannel (convolutionPair_zero_right f)).trans
    completedBoundaryReducedChannel_zero

/-- The zero Hilbert source has zero self-pairing. -/
theorem completedBoundaryHilbertPairing_zero_zero :
    completedBoundaryHilbertPairing
        (0 : CompletedBoundaryHilbertSource)
        (0 : CompletedBoundaryHilbertSource) =
      0 := by
  unfold completedBoundaryHilbertPairing
  change
    Complex.re
        (completedBoundaryReducedChannel
          (convolutionPair (0 : ZetaAdmissibleFunction) 0)) +
      0 * 0 =
    0
  calc
    Complex.re
        (completedBoundaryReducedChannel
          (convolutionPair (0 : ZetaAdmissibleFunction) 0)) +
      0 * 0 =
        Complex.re 0 + 0 * 0 := by
      exact congrArg
        (fun z : ℂ => Complex.re z + 0 * 0)
        completedBoundaryReducedChannel_convolutionPair_zero_zero
    _ = 0 + 0 * 0 := by
      exact congrArg (fun x : ℝ => x + 0 * 0) Complex.zero_re
    _ = 0 + 0 := by
      exact congrArg (fun x : ℝ => 0 + x) (zero_mul 0)
    _ = 0 := by
      exact zero_add 0

/-- The zero Hilbert source pairs trivially on the left. -/
theorem completedBoundaryHilbertPairing_zero_left
    (Y : CompletedBoundaryHilbertSource) :
    completedBoundaryHilbertPairing
        (0 : CompletedBoundaryHilbertSource)
        Y =
      0 := by
  unfold completedBoundaryHilbertPairing
  change
    Complex.re
        (completedBoundaryReducedChannel
          (convolutionPair (0 : ZetaAdmissibleFunction) Y.seed)) +
      0 * Y.correctionCoordinate =
    0
  calc
    Complex.re
        (completedBoundaryReducedChannel
          (convolutionPair (0 : ZetaAdmissibleFunction) Y.seed)) +
      0 * Y.correctionCoordinate =
        Complex.re 0 + 0 * Y.correctionCoordinate := by
      exact congrArg
        (fun z : ℂ => Complex.re z + 0 * Y.correctionCoordinate)
        (completedBoundaryReducedChannel_convolutionPair_zero_left Y.seed)
    _ = 0 + 0 * Y.correctionCoordinate := by
      exact congrArg (fun x : ℝ => x + 0 * Y.correctionCoordinate) Complex.zero_re
    _ = 0 + 0 := by
      exact congrArg (fun x : ℝ => 0 + x) (zero_mul Y.correctionCoordinate)
    _ = 0 := by
      exact zero_add 0

/-- The zero Hilbert source pairs trivially on the right. -/
theorem completedBoundaryHilbertPairing_zero_right
    (X : CompletedBoundaryHilbertSource) :
    completedBoundaryHilbertPairing
        X
        (0 : CompletedBoundaryHilbertSource) =
      0 := by
  unfold completedBoundaryHilbertPairing
  change
    Complex.re
        (completedBoundaryReducedChannel
          (convolutionPair X.seed (0 : ZetaAdmissibleFunction))) +
      X.correctionCoordinate * 0 =
    0
  calc
    Complex.re
        (completedBoundaryReducedChannel
          (convolutionPair X.seed (0 : ZetaAdmissibleFunction))) +
      X.correctionCoordinate * 0 =
        Complex.re 0 + X.correctionCoordinate * 0 := by
      exact congrArg
        (fun z : ℂ => Complex.re z + X.correctionCoordinate * 0)
        (completedBoundaryReducedChannel_convolutionPair_zero_right X.seed)
    _ = 0 + X.correctionCoordinate * 0 := by
      exact congrArg (fun x : ℝ => x + X.correctionCoordinate * 0) Complex.zero_re
    _ = 0 + 0 := by
      exact congrArg (fun x : ℝ => 0 + x) (mul_zero X.correctionCoordinate)
    _ = 0 := by
      exact zero_add 0

/-- The zero Hilbert source is lower-weight radical. -/
theorem completedBoundaryHilbertSource_zero_lowerWeightRadical :
    CompletedBoundaryHilbertSource.LowerWeightRadical
      (0 : CompletedBoundaryHilbertSource) := by
  intro T
  exact
    ⟨completedBoundaryHilbertPairing_zero_left T,
      completedBoundaryHilbertPairing_zero_right T⟩

/-- Adding a lower-weight radical Hilbert source does not change the reduced time-pairing
scalar, provided the completed Hilbert pairing is additive in both variables. -/
theorem completedBoundaryTimePairingScalar_eq_of_add_lowerWeightRadical
    (B_add_left :
      ∀ x y z : CompletedBoundaryHilbertSource,
        completedBoundaryHilbertPairing (x + y) z =
          completedBoundaryHilbertPairing x z +
            completedBoundaryHilbertPairing y z)
    (B_add_right :
      ∀ x y z : CompletedBoundaryHilbertSource,
        completedBoundaryHilbertPairing x (y + z) =
          completedBoundaryHilbertPairing x y +
            completedBoundaryHilbertPairing x z)
    (Y D : CompletedBoundaryHilbertSource)
    (hD : CompletedBoundaryHilbertSource.LowerWeightRadical D) :
    completedBoundaryTimePairingScalar (Y + D) =
      completedBoundaryTimePairingScalar Y := by
  have hDYD :
      completedBoundaryHilbertPairing D (Y + D) = 0 :=
    (hD (Y + D)).1
  have hYD :
      completedBoundaryHilbertPairing Y D = 0 :=
    (hD Y).2
  unfold completedBoundaryTimePairingScalar
  calc
    completedBoundaryHilbertPairing (Y + D) (Y + D) =
        completedBoundaryHilbertPairing Y (Y + D) +
          completedBoundaryHilbertPairing D (Y + D) := by
      exact B_add_left Y D (Y + D)
    _ =
        completedBoundaryHilbertPairing Y (Y + D) + 0 := by
      exact congrArg
        (fun x : ℝ => completedBoundaryHilbertPairing Y (Y + D) + x)
        hDYD
    _ =
        completedBoundaryHilbertPairing Y (Y + D) := by
      exact add_zero (completedBoundaryHilbertPairing Y (Y + D))
    _ =
        completedBoundaryHilbertPairing Y Y +
          completedBoundaryHilbertPairing Y D := by
      exact B_add_right Y Y D
    _ =
        completedBoundaryHilbertPairing Y Y + 0 := by
      exact congrArg
        (fun x : ℝ => completedBoundaryHilbertPairing Y Y + x)
        hYD
    _ =
        completedBoundaryHilbertPairing Y Y := by
      exact add_zero (completedBoundaryHilbertPairing Y Y)

/-- The additive decomposition `X = Y + (X - Y)` for Hilbert sources. -/
theorem completedBoundaryHilbertSource_eq_add_sub
    (X Y : CompletedBoundaryHilbertSource) :
    X = Y + (X - Y) := by
  have h :
      Y + (X - Y) = X := by
    calc
      Y + (X - Y) =
          Y + (X + -Y) := by
        rfl
      _ =
          (Y + X) + -Y := by
        exact (add_assoc Y X (-Y)).symm
      _ =
          (X + Y) + -Y := by
        exact congrArg (fun Z : CompletedBoundaryHilbertSource => Z + -Y)
          (add_comm Y X)
      _ =
          X + (Y + -Y) := by
        exact add_assoc X Y (-Y)
      _ =
          X + 0 := by
        exact congrArg (fun Z : CompletedBoundaryHilbertSource => X + Z)
          (add_right_neg Y)
      _ =
          X := by
        exact add_zero X
  exact h.symm

/-- Two Hilbert-source representatives have the same reduced time-pairing scalar when their
difference is lower-weight radical, provided the completed Hilbert pairing is additive in both
variables. -/
theorem completedBoundaryTimePairingScalar_eq_of_lowerWeightRadical_sub
    (B_add_left :
      ∀ x y z : CompletedBoundaryHilbertSource,
        completedBoundaryHilbertPairing (x + y) z =
          completedBoundaryHilbertPairing x z +
            completedBoundaryHilbertPairing y z)
    (B_add_right :
      ∀ x y z : CompletedBoundaryHilbertSource,
        completedBoundaryHilbertPairing x (y + z) =
          completedBoundaryHilbertPairing x y +
            completedBoundaryHilbertPairing x z)
    (X Y : CompletedBoundaryHilbertSource)
    (hD : CompletedBoundaryHilbertSource.LowerWeightRadical (X - Y)) :
    completedBoundaryTimePairingScalar X =
      completedBoundaryTimePairingScalar Y := by
  have hdecomp : X = Y + (X - Y) :=
    completedBoundaryHilbertSource_eq_add_sub X Y
  calc
    completedBoundaryTimePairingScalar X =
        completedBoundaryTimePairingScalar (Y + (X - Y)) := by
      exact congrArg completedBoundaryTimePairingScalar hdecomp
    _ =
        completedBoundaryTimePairingScalar Y := by
      exact completedBoundaryTimePairingScalar_eq_of_add_lowerWeightRadical
        B_add_left
        B_add_right
        Y
        (X - Y)
        hD

/-- Rearranging the real parts of the reduced channel plus pole channel. -/
theorem completedBoundaryReduced_re_add_pole_re
    (p a q r : ℂ) :
    Complex.re (p + a + r) + Complex.re q =
      Complex.re (p + a + q + r) := by
  calc
    Complex.re (p + a + r) + Complex.re q =
        (Complex.re (p + a) + Complex.re r) + Complex.re q := by
      exact congrArg (fun x : ℝ => x + Complex.re q)
        (Complex.add_re (p + a) r)
    _ =
        (Complex.re p + Complex.re a + Complex.re r) + Complex.re q := by
      exact congrArg (fun x : ℝ => (x + Complex.re r) + Complex.re q)
        (Complex.add_re p a)
    _ =
        Complex.re p + Complex.re a + Complex.re q + Complex.re r := by
      ring
    _ =
        Complex.re (p + a + q) + Complex.re r := by
      exact congrArg (fun x : ℝ => x + Complex.re r)
        ((congrArg (fun x : ℝ => x + Complex.re q)
          (Complex.add_re p a)).symm)
    _ =
        Complex.re (p + a + q + r) := by
      exact (Complex.add_re (p + a + q) r).symm

/-- The Hilbert pairing of a realized seed with itself is the real completed boundary
channel on its autocorrelation probe.  The affine pole/correction contribution is represented
by the explicit correction coordinate in `CompletedBoundaryHilbertSource`. -/
theorem completedBoundaryHilbertPairing_source_self_eq_boundaryChannel_re
    (f : ZetaAdmissibleFunction) :
    completedBoundaryHilbertPairing
        (completedBoundaryHilbertSource f)
        (completedBoundaryHilbertSource f) =
      Complex.re (completedBoundaryChannel (convolutionAutocorrelation f)) := by
  let g : ZetaAdmissibleFunction := convolutionAutocorrelation f
  let p : ℂ := primeBoundaryChannel g
  let a : ℂ := archimedeanBoundaryChannel g
  let q : ℂ := poleBoundaryChannel g
  let r : ℂ := completionBoundaryChannel g
  have hconv : convolutionPair f f = g := by
    unfold g
    exact convolutionPair_self f
  have hcorr :
      zetaCompletionCorrectionPacketCoordinate *
          zetaCompletionCorrectionPacketCoordinate =
        Complex.re q := by
    unfold q
    unfold g
    exact (zetaCorrectionAutocorrelationChannel_eq_squareEnergy f).symm
  have hchannel :
      completedBoundaryChannel g = p + a + q + r := by
    unfold p
    unfold a
    unfold q
    unfold r
    exact completedBoundaryChannel_eq_prime_add_archimedean_add_pole_add_completion g
  have hreduced :
      primeBoundaryChannel (convolutionPair f f) +
          archimedeanBoundaryChannel (convolutionPair f f) +
          completionBoundaryChannel (convolutionPair f f) =
        p + a + r := by
    calc
      primeBoundaryChannel (convolutionPair f f) +
          archimedeanBoundaryChannel (convolutionPair f f) +
          completionBoundaryChannel (convolutionPair f f) =
        primeBoundaryChannel g +
            archimedeanBoundaryChannel g +
            completionBoundaryChannel g := by
        exact congrArg
          (fun u : ZetaAdmissibleFunction =>
            primeBoundaryChannel u + archimedeanBoundaryChannel u +
              completionBoundaryChannel u)
          hconv
      _ = p + a + r := by
        rfl
  unfold completedBoundaryHilbertPairing
  unfold completedBoundaryHilbertSource
  unfold completedBoundaryReducedChannel
  calc
    Complex.re
          (primeBoundaryChannel (convolutionPair f f) +
            archimedeanBoundaryChannel (convolutionPair f f) +
            completionBoundaryChannel (convolutionPair f f)) +
        zetaCompletionCorrectionPacketCoordinate *
          zetaCompletionCorrectionPacketCoordinate =
        Complex.re (p + a + r) +
          zetaCompletionCorrectionPacketCoordinate *
            zetaCompletionCorrectionPacketCoordinate := by
      exact congrArg₂ HAdd.hAdd
        (congrArg Complex.re hreduced)
        rfl
    _ = Complex.re (p + a + r) + Complex.re q := by
      exact congrArg
        (fun x : ℝ => Complex.re (p + a + r) + x)
        hcorr
    _ = Complex.re (p + a + q + r) := by
      exact completedBoundaryReduced_re_add_pole_re p a q r
    _ = Complex.re (completedBoundaryChannel g) := by
      exact congrArg Complex.re hchannel.symm

/-- The finite lower-weight exact component consisting of diagonal debt plus its absorption
channel.  Its finite-part representative is identically zero. -/
def finiteBoundaryLowerWeightExactObject
    (N : ℕ) (f : ZetaAdmissibleFunction) : FiniteBoundaryWeightObject :=
  { positiveSquare := 0
    primeCross := 0
    diagonalDebt := zetaPrimeDiagonalDebt N f
    debtAbsorption := finitePartDebtAbsorptionWindow N f
    archCorrection := 0 }

/-- A finite boundary packet is lower-weight exact when its finite-part representative is
zero. -/
structure FiniteBoundaryLowerWeightExactCert
    (x : FiniteBoundaryWeightObject) where
  finitePart_eq_zero :
    FiniteBoundaryWeightObject.finitePartRepresentative x = 0

/-- The concrete diagonal-debt plus debt-absorption packet is finite lower-weight exact. -/
def finiteBoundaryLowerWeightExactObject_cert
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    FiniteBoundaryLowerWeightExactCert
      (finiteBoundaryLowerWeightExactObject N f) :=
  { finitePart_eq_zero := by
      unfold finiteBoundaryLowerWeightExactObject
      unfold FiniteBoundaryWeightObject.finitePartRepresentative
      unfold finitePartDebtAbsorptionWindow
      let D : ℝ := zetaPrimeDiagonalDebt N f
      change 0 + D + -D + 0 = 0
      calc
        0 + D + -D + 0 = D + -D + 0 := by
          exact congrArg (fun x : ℝ => x + -D + 0) (zero_add D)
        _ = 0 + 0 := by
          exact congrArg (fun x : ℝ => x + 0) (add_neg_cancel D)
        _ = 0 := by
          exact zero_add 0 }

/-- A completed boundary stream realized in the Hilbert pairing. -/
structure CompletedBoundaryHilbertWeightStream where
  source : CompletedBoundaryHilbertSource
  object : ℕ → FiniteBoundaryWeightObject
  scalar : ℝ
  scalar_eq_pairing_self :
    scalar = completedBoundaryHilbertPairing source source
  finitePart_tendsto_scalar :
    Tendsto
      (fun N : ℕ =>
        FiniteBoundaryWeightObject.finitePartRepresentative (object N))
      atTop
      (𝓝 scalar)

namespace CompletedBoundaryHilbertWeightStream

/-- A Hilbert stream is lower-weight exact when its scalar realization is zero. -/
def IsLowerWeightExact
    (D : CompletedBoundaryHilbertWeightStream) : Prop :=
  D.scalar = 0

/-- A Hilbert stream is lower-weight null when it lies in the radical of the Hilbert pairing. -/
def IsLowerWeightNull
    (D : CompletedBoundaryHilbertWeightStream) : Prop :=
  ∀ T : CompletedBoundaryHilbertWeightStream,
    completedBoundaryHilbertPairing D.source T.source = 0 ∧
      completedBoundaryHilbertPairing T.source D.source = 0

/-- Lower-weight exactness gives diagonal nullity in the Hilbert pairing. -/
theorem IsLowerWeightExact.pairing_self_eq_zero
    {D : CompletedBoundaryHilbertWeightStream}
    (hD : IsLowerWeightExact D) :
    completedBoundaryHilbertPairing D.source D.source = 0 := by
  exact D.scalar_eq_pairing_self.symm.trans hD

end CompletedBoundaryHilbertWeightStream

/-- The completed Hilbert weight stream attached to an admissible seed. -/
def completedBoundaryHilbertWeightStream
    (f : ZetaAdmissibleFunction) : CompletedBoundaryHilbertWeightStream :=
  { source := completedBoundaryHilbertSource f
    object := fun N : ℕ => finiteBoundaryWeightObject N f
    scalar := Complex.re (completedBoundaryChannel (convolutionAutocorrelation f))
    scalar_eq_pairing_self :=
      (completedBoundaryHilbertPairing_source_self_eq_boundaryChannel_re f).symm
    finitePart_tendsto_scalar := by
      have hfinite :
          Tendsto
            (fun N : ℕ => finitePartBoundaryWindow N f)
            atTop
            (𝓝 (Complex.re (completedBoundaryChannel (convolutionAutocorrelation f)))) :=
        finitePartBoundaryWindow_tendsto_boundaryChannel f
      have hobject :
          (fun N : ℕ =>
            FiniteBoundaryWeightObject.finitePartRepresentative
              (finiteBoundaryWeightObject N f)) =
            (fun N : ℕ => finitePartBoundaryWindow N f) := by
        funext N
        exact finiteBoundaryWeightObject_finitePartRepresentative_eq_finitePartBoundaryWindow
          N f
      exact Eq.subst
        (motive := fun u : ℕ → ℝ =>
          Tendsto u atTop
            (𝓝 (Complex.re (completedBoundaryChannel (convolutionAutocorrelation f)))))
        hobject.symm
        hfinite }

/-- The finite lower-weight exact component has zero finite-part representative. -/
theorem finiteBoundaryLowerWeightExactObject_finitePart_eq_zero
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    FiniteBoundaryWeightObject.finitePartRepresentative
        (finiteBoundaryLowerWeightExactObject N f) =
      0 :=
  (finiteBoundaryLowerWeightExactObject_cert N f).finitePart_eq_zero

/-- The completed lower-weight exact stream has zero finite-part representatives. -/
theorem completedBoundaryLowerWeightExact_finitePart_eq_zero
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    FiniteBoundaryWeightObject.finitePartRepresentative
        (finiteBoundaryLowerWeightExactObject N f) =
      0 :=
  finiteBoundaryLowerWeightExactObject_finitePart_eq_zero N f

/-- The concrete source-probe package for the lower-weight exact diagonal-debt cancellation
component.  It records the actual Hilbert source and the actual finite window component; no
cross-pairing vanishing is built into this object. -/
structure CompletedBoundaryLowerWeightExactSourceProbe
    (f : ZetaAdmissibleFunction) where
  source : CompletedBoundaryHilbertSource
  object : ℕ → FiniteBoundaryWeightObject
  source_eq_zero :
    source = completedBoundaryLowerWeightExactHilbertSource
  object_eq_exact :
    object = fun N : ℕ => finiteBoundaryLowerWeightExactObject N f
  finitePart_eq_zero :
    ∀ N : ℕ,
      FiniteBoundaryWeightObject.finitePartRepresentative (object N) = 0

/-- The diagonal-debt plus debt-absorption cancellation packet is represented by the zero
Hilbert source at the finite-window level. -/
def completedBoundaryLowerWeightExactSourceProbe
    (f : ZetaAdmissibleFunction) :
    CompletedBoundaryLowerWeightExactSourceProbe f :=
  { source := completedBoundaryLowerWeightExactHilbertSource
    object := fun N : ℕ => finiteBoundaryLowerWeightExactObject N f
    source_eq_zero := rfl
    object_eq_exact := rfl
    finitePart_eq_zero := by
      intro N
      exact finiteBoundaryLowerWeightExactObject_finitePart_eq_zero N f }

/-- The lower-weight exact source probe has zero finite scalar at every cutoff. -/
theorem completedBoundaryLowerWeightExactSourceProbe_finitePart_eq_zero
    (f : ZetaAdmissibleFunction) (N : ℕ) :
    FiniteBoundaryWeightObject.finitePartRepresentative
        ((completedBoundaryLowerWeightExactSourceProbe f).object N) =
      0 :=
  (completedBoundaryLowerWeightExactSourceProbe f).finitePart_eq_zero N

/-- The completed Hilbert stream represented by the lower-weight exact diagonal-debt
cancellation component. -/
def completedBoundaryLowerWeightExactHilbertWeightStream
    (f : ZetaAdmissibleFunction) :
    CompletedBoundaryHilbertWeightStream :=
  { source := (completedBoundaryLowerWeightExactSourceProbe f).source
    object := (completedBoundaryLowerWeightExactSourceProbe f).object
    scalar := 0
    scalar_eq_pairing_self := by
      have hsource :
          (completedBoundaryLowerWeightExactSourceProbe f).source =
            (0 : CompletedBoundaryHilbertSource) :=
        (completedBoundaryLowerWeightExactSourceProbe f).source_eq_zero
      change
        0 =
          completedBoundaryHilbertPairing
            (completedBoundaryLowerWeightExactSourceProbe f).source
            (completedBoundaryLowerWeightExactSourceProbe f).source
      calc
        0 =
            completedBoundaryHilbertPairing
              (0 : CompletedBoundaryHilbertSource)
              (0 : CompletedBoundaryHilbertSource) := by
          exact completedBoundaryHilbertPairing_zero_zero.symm
        _ =
            completedBoundaryHilbertPairing
              (completedBoundaryLowerWeightExactSourceProbe f).source
              (completedBoundaryLowerWeightExactSourceProbe f).source := by
          exact congrArg₂ completedBoundaryHilbertPairing hsource.symm hsource.symm
    finitePart_tendsto_scalar := by
      have hzero :
          (fun N : ℕ =>
            FiniteBoundaryWeightObject.finitePartRepresentative
              ((completedBoundaryLowerWeightExactSourceProbe f).object N)) =
            fun _N : ℕ => 0 := by
        funext N
        exact completedBoundaryLowerWeightExactSourceProbe_finitePart_eq_zero f N
      exact Eq.subst
        (motive := fun u : ℕ → ℝ => Tendsto u atTop (𝓝 0))
        hzero.symm
        tendsto_const_nhds }

/-- The lower-weight exact Hilbert stream has zero scalar. -/
theorem completedBoundaryLowerWeightExactHilbertWeightStream_scalar_eq_zero
    (f : ZetaAdmissibleFunction) :
    (completedBoundaryLowerWeightExactHilbertWeightStream f).scalar = 0 := by
  rfl

/-- The lower-weight exact Hilbert stream is lower-weight exact. -/
theorem completedBoundaryLowerWeightExactHilbertWeightStream_isLowerWeightExact
    (f : ZetaAdmissibleFunction) :
    CompletedBoundaryHilbertWeightStream.IsLowerWeightExact
      (completedBoundaryLowerWeightExactHilbertWeightStream f) := by
  rfl

/-- Any completed Hilbert stream with zero source is lower-weight null. -/
theorem completedBoundaryHilbertWeightStream_isLowerWeightNull_of_source_eq_zero
    (D : CompletedBoundaryHilbertWeightStream)
    (hD : D.source = (0 : CompletedBoundaryHilbertSource)) :
    CompletedBoundaryHilbertWeightStream.IsLowerWeightNull D := by
  intro T
  constructor
  · calc
      completedBoundaryHilbertPairing D.source T.source =
          completedBoundaryHilbertPairing (0 : CompletedBoundaryHilbertSource) T.source := by
        exact congrArg (fun X : CompletedBoundaryHilbertSource =>
          completedBoundaryHilbertPairing X T.source) hD
      _ = 0 := by
        exact completedBoundaryHilbertPairing_zero_left T.source
  · calc
      completedBoundaryHilbertPairing T.source D.source =
          completedBoundaryHilbertPairing T.source (0 : CompletedBoundaryHilbertSource) := by
        exact congrArg (fun X : CompletedBoundaryHilbertSource =>
          completedBoundaryHilbertPairing T.source X) hD
      _ = 0 := by
        exact completedBoundaryHilbertPairing_zero_right T.source

/-- The concrete diagonal-debt cancellation stream is lower-weight null. -/
theorem completedBoundaryLowerWeightExactHilbertWeightStream_isLowerWeightNull_unconditional
    (f : ZetaAdmissibleFunction) :
    CompletedBoundaryHilbertWeightStream.IsLowerWeightNull
      (completedBoundaryLowerWeightExactHilbertWeightStream f) := by
  exact completedBoundaryHilbertWeightStream_isLowerWeightNull_of_source_eq_zero
    (completedBoundaryLowerWeightExactHilbertWeightStream f)
    (completedBoundaryLowerWeightExactSourceProbe f).source_eq_zero


/-- The completed boundary pairing is induced by the two-variable completed boundary kernel. -/
def completedBoundaryPairing
    (S T : CompletedBoundaryWeightStream) : ℝ :=
  Complex.re (completedBoundaryChannel (convolutionPair S.source T.source))

/-- The completed boundary pairing unfolds to the real part of the completed Hermitian
kernel. -/
theorem completedBoundaryPairing_eq_kernel
    (S T : CompletedBoundaryWeightStream) :
    completedBoundaryPairing S T =
      Complex.re (completedHermitianKernel S.source T.source) := by
  unfold completedBoundaryPairing
  exact congrArg Complex.re
    (completedBoundaryChannel_convolutionPair_eq_kernel S.source T.source)

/-- The diagonal of the completed boundary pairing is the completed boundary channel on the
convolution autocorrelation probe. -/
theorem completedBoundaryPairing_self_eq_boundaryChannel_autocorrelation
    (S : CompletedBoundaryWeightStream) :
    completedBoundaryPairing S S =
      Complex.re (completedBoundaryChannel (convolutionAutocorrelation S.source)) := by
  unfold completedBoundaryPairing
  exact congrArg
    (fun g : ZetaAdmissibleFunction =>
      Complex.re (completedBoundaryChannel g))
    (convolutionPair_self S.source)

/-- The scalar of a completed boundary weight stream is the self-pairing of its completed
boundary kernel. -/
theorem completedBoundaryWeightStream_scalar_eq_pairing_self
    (S : CompletedBoundaryWeightStream) :
    S.scalar = completedBoundaryPairing S S := by
  exact S.scalar_eq_completedBoundaryChannel.trans
    (completedBoundaryPairing_self_eq_boundaryChannel_autocorrelation S).symm

namespace CompletedBoundaryWeightStream

/-- A completed boundary weight stream is lower-weight null when it lies in the radical of
the completed boundary pairing. -/
def IsLowerWeightNull
    (D : CompletedBoundaryWeightStream) : Prop :=
  ∀ T : CompletedBoundaryWeightStream,
    completedBoundaryPairing D T = 0 ∧
      completedBoundaryPairing T D = 0

/-- A completed boundary weight stream is lower-weight exact when its completed diagonal
realization is zero.  This is the diagonal form of lower-weight absorption; positive
semidefiniteness of the completed pairing upgrades it to radical/nullity. -/
def IsLowerWeightExact
    (D : CompletedBoundaryWeightStream) : Prop :=
  D.scalar = 0

/-- A lower-weight null stream pairs trivially on the left. -/
theorem IsLowerWeightNull.pairing_left_eq_zero
    {D T : CompletedBoundaryWeightStream}
    (hD : IsLowerWeightNull D) :
    completedBoundaryPairing D T = 0 :=
  (hD T).1

/-- A lower-weight null stream pairs trivially on the right. -/
theorem IsLowerWeightNull.pairing_right_eq_zero
    {D T : CompletedBoundaryWeightStream}
    (hD : IsLowerWeightNull D) :
    completedBoundaryPairing T D = 0 :=
  (hD T).2

/-- A lower-weight null stream has zero self-pairing. -/
theorem IsLowerWeightNull.pairing_self_eq_zero
    {D : CompletedBoundaryWeightStream}
    (hD : IsLowerWeightNull D) :
    completedBoundaryPairing D D = 0 :=
  (hD D).1

/-- A lower-weight exact stream has zero completed self-pairing. -/
theorem IsLowerWeightExact.pairing_self_eq_zero
    {D : CompletedBoundaryWeightStream}
    (hD : IsLowerWeightExact D) :
    completedBoundaryPairing D D = 0 := by
  exact (completedBoundaryWeightStream_scalar_eq_pairing_self D).symm.trans hD

end CompletedBoundaryWeightStream

/-- In a real symmetric positive-semidefinite bilinear pairing, a vector with zero
self-pairing lies in the left radical.

This is the algebraic reduction that turns diagonal lower-weight nullity into cross-kernel
nullity.  The analytic work for the completed boundary pairing is to provide the bilinear,
symmetric, and positive-semidefinite laws for the concrete kernel. -/
theorem real_symmetric_bilinear_psd_left_radical_of_self_zero
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (B : V → V → ℝ)
    (B_add_left : ∀ x y z : V, B (x + y) z = B x z + B y z)
    (B_smul_left : ∀ (a : ℝ) (x y : V), B (a • x) y = a * B x y)
    (B_add_right : ∀ x y z : V, B x (y + z) = B x y + B x z)
    (B_smul_right : ∀ (a : ℝ) (x y : V), B x (a • y) = a * B x y)
    (B_symm : ∀ x y : V, B x y = B y x)
    (B_psd : ∀ x : V, 0 ≤ B x x)
    {d t : V}
    (hdd : B d d = 0) :
    B d t = 0 := by
  by_cases htd : B t d = 0
  · exact (B_symm d t).trans htd
  · exfalso
    let b : ℝ := B t t
    let c : ℝ := B t d
    let r : ℝ := -((b + 1) / (2 * c))
    have hc : c ≠ 0 := htd
    have hpos : 0 ≤ B (t + r • d) (t + r • d) :=
      B_psd (t + r • d)
    have hcross : B d t = c := by
      exact B_symm d t
    have hexpand :
        B (t + r • d) (t + r • d) =
          b + 2 * r * c := by
      calc
        B (t + r • d) (t + r • d) =
            B t (t + r • d) + B (r • d) (t + r • d) := by
          exact B_add_left t (r • d) (t + r • d)
        _ =
            (B t t + B t (r • d)) +
              (B (r • d) t + B (r • d) (r • d)) := by
          exact congrArg₂ HAdd.hAdd
            (B_add_right t t (r • d))
            (B_add_right (r • d) t (r • d))
        _ =
            (b + r * c) + (r * c + r * (r * 0)) := by
          exact congrArg₂ HAdd.hAdd
            (congrArg₂ HAdd.hAdd rfl (B_smul_right r t d))
            ((congrArg₂ HAdd.hAdd
              (B_smul_left r d t)
              ((B_smul_left r d (r • d)).trans
                (congrArg (fun x : ℝ => r * x)
                  ((B_smul_right r d d).trans
                    (congrArg (fun x : ℝ => r * x) hdd))))).trans
              (congrArg₂ HAdd.hAdd
                (congrArg (fun x : ℝ => r * x) hcross)
                rfl))
        _ = b + 2 * r * c := by
          ring
    have hr : b + 2 * r * c = -1 := by
      unfold r
      field_simp [hc]
      ring
    rw [hexpand, hr] at hpos
    linarith

/-- In a real symmetric positive-semidefinite bilinear pairing, a vector with zero
self-pairing lies in the right radical. -/
theorem real_symmetric_bilinear_psd_right_radical_of_self_zero
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (B : V → V → ℝ)
    (B_add_left : ∀ x y z : V, B (x + y) z = B x z + B y z)
    (B_smul_left : ∀ (a : ℝ) (x y : V), B (a • x) y = a * B x y)
    (B_add_right : ∀ x y z : V, B x (y + z) = B x y + B x z)
    (B_smul_right : ∀ (a : ℝ) (x y : V), B x (a • y) = a * B x y)
    (B_symm : ∀ x y : V, B x y = B y x)
    (B_psd : ∀ x : V, 0 ≤ B x x)
    {d t : V}
    (hdd : B d d = 0) :
    B t d = 0 := by
  have hleft :
      B d t = 0 :=
    real_symmetric_bilinear_psd_left_radical_of_self_zero
      B B_add_left B_smul_left B_add_right B_smul_right B_symm B_psd hdd
  exact (B_symm t d).trans hleft

/-- Diagonal nullity implies left radicality for the completed Hilbert pairing. -/
theorem completedBoundaryHilbertPairing_left_zero_of_self_zero
    (B_add_left :
      ∀ x y z : CompletedBoundaryHilbertSource,
        completedBoundaryHilbertPairing (x + y) z =
          completedBoundaryHilbertPairing x z +
            completedBoundaryHilbertPairing y z)
    (B_smul_left :
      ∀ (a : ℝ) (x y : CompletedBoundaryHilbertSource),
        completedBoundaryHilbertPairing (a • x) y =
          a * completedBoundaryHilbertPairing x y)
    (B_add_right :
      ∀ x y z : CompletedBoundaryHilbertSource,
        completedBoundaryHilbertPairing x (y + z) =
          completedBoundaryHilbertPairing x y +
            completedBoundaryHilbertPairing x z)
    (B_smul_right :
      ∀ (a : ℝ) (x y : CompletedBoundaryHilbertSource),
        completedBoundaryHilbertPairing x (a • y) =
          a * completedBoundaryHilbertPairing x y)
    (B_symm :
      ∀ x y : CompletedBoundaryHilbertSource,
        completedBoundaryHilbertPairing x y =
          completedBoundaryHilbertPairing y x)
    (B_psd :
      ∀ x : CompletedBoundaryHilbertSource,
        0 ≤ completedBoundaryHilbertPairing x x)
    (D T : CompletedBoundaryHilbertWeightStream)
    (hDD : completedBoundaryHilbertPairing D.source D.source = 0) :
    completedBoundaryHilbertPairing D.source T.source = 0 := by
  exact
    real_symmetric_bilinear_psd_left_radical_of_self_zero
      completedBoundaryHilbertPairing
      B_add_left
      B_smul_left
      B_add_right
      B_smul_right
      B_symm
      B_psd
      (d := D.source)
      (t := T.source)
      hDD

/-- Diagonal nullity implies right radicality for the completed Hilbert pairing. -/
theorem completedBoundaryHilbertPairing_right_zero_of_self_zero
    (B_add_left :
      ∀ x y z : CompletedBoundaryHilbertSource,
        completedBoundaryHilbertPairing (x + y) z =
          completedBoundaryHilbertPairing x z +
            completedBoundaryHilbertPairing y z)
    (B_smul_left :
      ∀ (a : ℝ) (x y : CompletedBoundaryHilbertSource),
        completedBoundaryHilbertPairing (a • x) y =
          a * completedBoundaryHilbertPairing x y)
    (B_add_right :
      ∀ x y z : CompletedBoundaryHilbertSource,
        completedBoundaryHilbertPairing x (y + z) =
          completedBoundaryHilbertPairing x y +
            completedBoundaryHilbertPairing x z)
    (B_smul_right :
      ∀ (a : ℝ) (x y : CompletedBoundaryHilbertSource),
        completedBoundaryHilbertPairing x (a • y) =
          a * completedBoundaryHilbertPairing x y)
    (B_symm :
      ∀ x y : CompletedBoundaryHilbertSource,
        completedBoundaryHilbertPairing x y =
          completedBoundaryHilbertPairing y x)
    (B_psd :
      ∀ x : CompletedBoundaryHilbertSource,
        0 ≤ completedBoundaryHilbertPairing x x)
    (D T : CompletedBoundaryHilbertWeightStream)
    (hDD : completedBoundaryHilbertPairing D.source D.source = 0) :
    completedBoundaryHilbertPairing T.source D.source = 0 := by
  exact
    real_symmetric_bilinear_psd_right_radical_of_self_zero
      completedBoundaryHilbertPairing
      B_add_left
      B_smul_left
      B_add_right
      B_smul_right
      B_symm
      B_psd
      (d := D.source)
      (t := T.source)
      hDD

/-- Diagonal nullity of a Hilbert stream implies lower-weight nullity once the completed
Hilbert pairing has its symmetric bilinear positive-semidefinite laws. -/
theorem completedBoundaryHilbertWeightStream_isLowerWeightNull_of_self_pairing_zero
    (B_add_left :
      ∀ x y z : CompletedBoundaryHilbertSource,
        completedBoundaryHilbertPairing (x + y) z =
          completedBoundaryHilbertPairing x z +
            completedBoundaryHilbertPairing y z)
    (B_smul_left :
      ∀ (a : ℝ) (x y : CompletedBoundaryHilbertSource),
        completedBoundaryHilbertPairing (a • x) y =
          a * completedBoundaryHilbertPairing x y)
    (B_add_right :
      ∀ x y z : CompletedBoundaryHilbertSource,
        completedBoundaryHilbertPairing x (y + z) =
          completedBoundaryHilbertPairing x y +
            completedBoundaryHilbertPairing x z)
    (B_smul_right :
      ∀ (a : ℝ) (x y : CompletedBoundaryHilbertSource),
        completedBoundaryHilbertPairing x (a • y) =
          a * completedBoundaryHilbertPairing x y)
    (B_symm :
      ∀ x y : CompletedBoundaryHilbertSource,
        completedBoundaryHilbertPairing x y =
          completedBoundaryHilbertPairing y x)
    (B_psd :
      ∀ x : CompletedBoundaryHilbertSource,
        0 ≤ completedBoundaryHilbertPairing x x)
    (D : CompletedBoundaryHilbertWeightStream)
    (hDD : completedBoundaryHilbertPairing D.source D.source = 0) :
    CompletedBoundaryHilbertWeightStream.IsLowerWeightNull D := by
  intro T
  exact
    ⟨completedBoundaryHilbertPairing_left_zero_of_self_zero
        B_add_left B_smul_left B_add_right B_smul_right B_symm B_psd D T hDD,
      completedBoundaryHilbertPairing_right_zero_of_self_zero
        B_add_left B_smul_left B_add_right B_smul_right B_symm B_psd D T hDD⟩

/-- Lower-weight exact Hilbert streams lie in the radical/nullspace once the completed Hilbert
pairing has its symmetric bilinear positive-semidefinite laws. -/
theorem completedBoundaryHilbertWeightStream_isLowerWeightNull_of_lowerWeightExact
    (B_add_left :
      ∀ x y z : CompletedBoundaryHilbertSource,
        completedBoundaryHilbertPairing (x + y) z =
          completedBoundaryHilbertPairing x z +
            completedBoundaryHilbertPairing y z)
    (B_smul_left :
      ∀ (a : ℝ) (x y : CompletedBoundaryHilbertSource),
        completedBoundaryHilbertPairing (a • x) y =
          a * completedBoundaryHilbertPairing x y)
    (B_add_right :
      ∀ x y z : CompletedBoundaryHilbertSource,
        completedBoundaryHilbertPairing x (y + z) =
          completedBoundaryHilbertPairing x y +
            completedBoundaryHilbertPairing x z)
    (B_smul_right :
      ∀ (a : ℝ) (x y : CompletedBoundaryHilbertSource),
        completedBoundaryHilbertPairing x (a • y) =
          a * completedBoundaryHilbertPairing x y)
    (B_symm :
      ∀ x y : CompletedBoundaryHilbertSource,
        completedBoundaryHilbertPairing x y =
          completedBoundaryHilbertPairing y x)
    (B_psd :
      ∀ x : CompletedBoundaryHilbertSource,
        0 ≤ completedBoundaryHilbertPairing x x)
    (D : CompletedBoundaryHilbertWeightStream)
    (hD : CompletedBoundaryHilbertWeightStream.IsLowerWeightExact D) :
    CompletedBoundaryHilbertWeightStream.IsLowerWeightNull D := by
  exact completedBoundaryHilbertWeightStream_isLowerWeightNull_of_self_pairing_zero
    B_add_left
    B_smul_left
    B_add_right
    B_smul_right
    B_symm
    B_psd
    D
    (CompletedBoundaryHilbertWeightStream.IsLowerWeightExact.pairing_self_eq_zero hD)

/-- The concrete diagonal-debt cancellation stream is lower-weight null. -/
theorem completedBoundaryLowerWeightExactHilbertWeightStream_isLowerWeightNull
    (f : ZetaAdmissibleFunction) :
    CompletedBoundaryHilbertWeightStream.IsLowerWeightNull
      (completedBoundaryLowerWeightExactHilbertWeightStream f) := by
  exact completedBoundaryLowerWeightExactHilbertWeightStream_isLowerWeightNull_unconditional f

/-- A completed positive-boundary precone element.

The positive representative is the finite square-energy window.  The absorbed representative
is the finite representative after applying the finite diagonal-debt absorption normalization.
The scalar is the completed realization of that absorbed representative. -/
structure CompletedPositiveBoundaryPreconeElement where
  scalar : ℝ
  positiveRepresentative : ℕ → ℝ
  absorbedRepresentative : ℕ → ℝ
  absorptionDefect : ℕ → ℝ
  positiveRepresentative_nonnegative :
    ∀ N : ℕ, 0 ≤ positiveRepresentative N
  absorbedRepresentative_tendsto_scalar :
    Tendsto absorbedRepresentative atTop (𝓝 scalar)
  absorptionDefect_eq :
    ∀ N : ℕ,
      absorptionDefect N =
        absorbedRepresentative N - positiveRepresentative N

/-- The completed positive-boundary precone element attached to a zeta admissible function. -/
def completedPositiveBoundaryPreconeElement
    (f : ZetaAdmissibleFunction) : CompletedPositiveBoundaryPreconeElement :=
  { scalar :=
      Complex.re (completedBoundaryChannel (convolutionAutocorrelation f))
    positiveRepresentative :=
      fun N : ℕ => finitePositiveSquareEnergyWindow N f
    absorbedRepresentative :=
      fun N : ℕ => finitePositiveRenormalizedBoundaryWindow N f
    absorptionDefect :=
      fun N : ℕ => finiteDiagonalDebtAbsorptionDefect N f
    positiveRepresentative_nonnegative :=
      fun N : ℕ => finitePositiveSquareEnergyWindow_nonnegative N f
    absorbedRepresentative_tendsto_scalar :=
      finitePositiveRenormalizedBoundaryWindow_tendsto_boundaryChannel f
    absorptionDefect_eq := by
      intro N
      unfold finiteDiagonalDebtAbsorptionDefect
      rfl }

/-- The absorption defect of the completed positive-boundary precone element is the finite
debt-absorption channel. -/
theorem completedPositiveBoundaryPreconeElement_absorptionDefect_eq_debtAbsorption
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    (completedPositiveBoundaryPreconeElement f).absorptionDefect N =
      finitePartDebtAbsorptionWindow N f := by
  exact finiteDiagonalDebtAbsorptionDefect_eq_finitePartDebtAbsorptionWindow N f

/-- The scalar realization of the completed positive-boundary precone element is the real
completed boundary channel on the convolution-autocorrelation probe. -/
theorem completedPositiveBoundaryPreconeElement_scalar_eq_boundaryChannel_re
    (f : ZetaAdmissibleFunction) :
    (completedPositiveBoundaryPreconeElement f).scalar =
      Complex.re (completedBoundaryChannel (convolutionAutocorrelation f)) := by
  rfl

/-- The ordered-heart class represented by the completed positive-boundary object.  Its scalar
is induced by `completedBoundaryHilbertPairing`, not by a separate analytic packet norm. -/
def completedPositiveBoundaryOrderedHeartClass
    (f : ZetaAdmissibleFunction) : CompletedBoundaryHilbertSource :=
  completedBoundaryHilbertSource f

/-- The scalar realization of the completed positive-boundary precone element is the reduced
time-pairing scalar of its completed Hilbert source. -/
theorem completedPositiveBoundaryPreconeElement_scalar_eq_timePairingScalar
    (f : ZetaAdmissibleFunction) :
    (completedPositiveBoundaryPreconeElement f).scalar =
      completedBoundaryTimePairingScalar
        (completedPositiveBoundaryOrderedHeartClass f) := by
  have hscalar :
      (completedPositiveBoundaryPreconeElement f).scalar =
        Complex.re (completedBoundaryChannel (convolutionAutocorrelation f)) :=
    completedPositiveBoundaryPreconeElement_scalar_eq_boundaryChannel_re f
  have hpair :
      completedBoundaryTimePairingScalar
          (completedPositiveBoundaryOrderedHeartClass f) =
        Complex.re (completedBoundaryChannel (convolutionAutocorrelation f)) := by
    unfold completedPositiveBoundaryOrderedHeartClass
    unfold completedBoundaryTimePairingScalar
    exact completedBoundaryHilbertPairing_source_self_eq_boundaryChannel_re f
  exact hscalar.trans hpair.symm

/-- The ordered-heart class represented by the completed finite-part boundary channel.

The raw finite-part scalar is the time-side representative.  Its class in the completed
ordered heart is the absorbed positive-defect class after lower-weight diagonal-debt
transport. -/
def completedFinitePartBoundaryOrderedHeartClass
    (f : ZetaAdmissibleFunction) : CompletedBoundaryHilbertSource :=
  completedPositiveBoundaryOrderedHeartClass f

/-- The raw finite-part scalar realizes as the time-pairing scalar of its ordered-heart
representative. -/
theorem completedFinitePartBoundaryChannel_eq_timePairingScalar
    (f : ZetaAdmissibleFunction) :
    completedFinitePartBoundaryChannel f =
      completedBoundaryTimePairingScalar
        (completedFinitePartBoundaryOrderedHeartClass f) := by
  have hfinite :
      completedFinitePartBoundaryChannel f =
        Complex.re (completedBoundaryChannel (convolutionAutocorrelation f)) :=
    completedFinitePartBoundaryChannel_eq_completedBoundaryChannel f
  have hpair :
      completedBoundaryTimePairingScalar
          (completedFinitePartBoundaryOrderedHeartClass f) =
        Complex.re (completedBoundaryChannel (convolutionAutocorrelation f)) := by
    unfold completedFinitePartBoundaryOrderedHeartClass
    exact
      (completedPositiveBoundaryPreconeElement_scalar_eq_timePairingScalar f).symm.trans
        (completedPositiveBoundaryPreconeElement_scalar_eq_boundaryChannel_re f)
  exact hfinite.trans hpair.symm

/-- The ordered-heart class represented by the positive square object.  It has the same
completed Hilbert-source representative as the absorbed finite-part class; the difference is
carried by the lower-weight radical absorption face. -/
def completedPositiveSquareBoundaryOrderedHeartClass
    (f : ZetaAdmissibleFunction) : CompletedBoundaryHilbertSource :=
  completedBoundaryHilbertSource f

/-- The ordered-heart class represented by the lower-weight absorption defect. -/
def completedPositiveBoundaryAbsorptionDefectOrderedHeartClass
    (_f : ZetaAdmissibleFunction) : CompletedBoundaryHilbertSource :=
  0

/-- The lower-weight absorption defect is radical in the completed ordered-heart quotient. -/
theorem completedPositiveBoundaryAbsorptionDefectOrderedHeartClass_lowerWeightRadical
    (f : ZetaAdmissibleFunction) :
    CompletedBoundaryHilbertSource.LowerWeightRadical
      (completedPositiveBoundaryAbsorptionDefectOrderedHeartClass f) := by
  unfold completedPositiveBoundaryAbsorptionDefectOrderedHeartClass
  exact completedBoundaryHilbertSource_zero_lowerWeightRadical

/-- The absorbed positive-boundary class and square-only class have the same ordered-heart
representative. -/
theorem completedPositiveBoundaryOrderedHeartClass_eq_square
    (f : ZetaAdmissibleFunction) :
    completedPositiveBoundaryOrderedHeartClass f =
      completedPositiveSquareBoundaryOrderedHeartClass f := by
  rfl

/-- The absorbed positive-boundary class and square-only class are GNS-tomographically
equivalent in the completed ordered heart. -/
theorem completedPositiveBoundaryOrderedHeartClass_GNSTomographicallyEquivalent_square
    (f : ZetaAdmissibleFunction) :
    CompletedBoundaryHilbertSource.GNSTomographicallyEquivalent
      (completedPositiveBoundaryOrderedHeartClass f)
      (completedPositiveSquareBoundaryOrderedHeartClass f) := by
  exact completedBoundaryHilbertSource_GNSTomography_of_eq
    (completedPositiveBoundaryOrderedHeartClass_eq_square f)

/-- The absorbed positive-boundary class and square-only class have the same ordered-heart
scalar by GNS tomography. -/
theorem completedPositiveBoundaryOrderedHeartScalar_eq_square_by_GNSTomography
    (f : ZetaAdmissibleFunction) :
    completedOrderedHeartScalar
        (completedPositiveBoundaryOrderedHeartClass f) =
      completedOrderedHeartScalar
        (completedPositiveSquareBoundaryOrderedHeartClass f) := by
  exact completedOrderedHeartScalar_eq_of_GNSTomography
    (completedPositiveBoundaryOrderedHeartClass_GNSTomographicallyEquivalent_square f)

/-- The finite-part boundary class is the absorbed positive-boundary class in the completed
ordered heart. -/
theorem completedFinitePartBoundaryOrderedHeartClass_eq_positiveBoundary
    (f : ZetaAdmissibleFunction) :
    completedFinitePartBoundaryOrderedHeartClass f =
      completedPositiveBoundaryOrderedHeartClass f := by
  rfl

/-- The finite-part boundary class is GNS-tomographically equivalent to the positive square
class.  This is the ordered-heart version of lower-weight diagonal-debt absorption. -/
theorem completedFinitePartBoundaryClass_GNSTomographicallyEquivalent_positiveSquare
    (f : ZetaAdmissibleFunction) :
    CompletedBoundaryHilbertSource.GNSTomographicallyEquivalent
      (completedFinitePartBoundaryOrderedHeartClass f)
      (completedPositiveSquareBoundaryOrderedHeartClass f) := by
  exact CompletedBoundaryHilbertSource.GNSTomographicallyEquivalent.trans
    (completedBoundaryHilbertSource_GNSTomography_of_eq
      (completedFinitePartBoundaryOrderedHeartClass_eq_positiveBoundary f))
    (completedPositiveBoundaryOrderedHeartClass_GNSTomographicallyEquivalent_square f)

/-- The finite-part boundary class has the same ordered-heart scalar as the positive square
class. -/
theorem completedFinitePartBoundaryOrderedHeartScalar_eq_positiveSquare
    (f : ZetaAdmissibleFunction) :
    completedOrderedHeartScalar
        (completedFinitePartBoundaryOrderedHeartClass f) =
      completedOrderedHeartScalar
        (completedPositiveSquareBoundaryOrderedHeartClass f) := by
  exact completedOrderedHeartScalar_eq_of_GNSTomography
    (completedFinitePartBoundaryClass_GNSTomographicallyEquivalent_positiveSquare f)

/-- If the reduced time-pairing scalar is reconstructed as the ordered-heart GNS scalar, then
the completed positive precone scalar is the ordered-heart scalar.  This representative-level
comparison is kept separate from the quotient-level ordered-heart scalar descent. -/
theorem completedPositiveBoundaryPreconeElement_scalar_eq_orderedHeartScalar_of_timePairingScalar_eq_orderedHeartScalar
    (f : ZetaAdmissibleFunction)
    (hcomparison :
      completedBoundaryTimePairingScalar
          (completedPositiveBoundaryOrderedHeartClass f) =
        completedOrderedHeartScalar
          (completedPositiveBoundaryOrderedHeartClass f)) :
    (completedPositiveBoundaryPreconeElement f).scalar =
      completedOrderedHeartScalar
        (completedPositiveBoundaryOrderedHeartClass f) := by
  exact
    (completedPositiveBoundaryPreconeElement_scalar_eq_timePairingScalar f).trans
      hcomparison

/-- The square-only ordered-heart scalar is the completed GNS norm-square. -/
theorem completedPositiveSquareBoundaryOrderedHeartScalar_eq_GNSNormSq
    (f : ZetaAdmissibleFunction) :
    completedOrderedHeartScalar
        (completedPositiveSquareBoundaryOrderedHeartClass f) =
      completedBoundaryGNSNormSq f := by
  unfold completedPositiveSquareBoundaryOrderedHeartClass
  exact (completedBoundaryGNSNormSq_eq_orderedHeartScalar f).symm

/-- The completed finite-part boundary class has GNS norm-square scalar in the completed
ordered heart. -/
theorem completedFinitePartBoundaryOrderedHeartScalar_eq_GNSNormSq
    (f : ZetaAdmissibleFunction) :
    completedOrderedHeartScalar
        (completedFinitePartBoundaryOrderedHeartClass f) =
      completedBoundaryGNSNormSq f := by
  exact
    (completedFinitePartBoundaryOrderedHeartScalar_eq_positiveSquare f).trans
      (completedPositiveSquareBoundaryOrderedHeartScalar_eq_GNSNormSq f)

/-- The completed finite-part boundary class has scalar represented by the completed
renormalized positive defect-kernel channel. -/
theorem completedFinitePartBoundaryOrderedHeartScalar_eq_renormalizedDefectKernel
    (f : ZetaAdmissibleFunction) :
    completedOrderedHeartScalar
        (completedFinitePartBoundaryOrderedHeartClass f) =
      completedRenormalizedDefectKernelBoundaryChannel f := by
  exact
    (completedFinitePartBoundaryOrderedHeartScalar_eq_GNSNormSq f).trans
      (completedRenormalizedDefectKernelBoundaryChannel_eq_GNSNormSq f).symm

/-- The completed ordered-heart quotient class represented by the finite-part boundary
channel after lower-weight absorption. -/
def completedFinitePartBoundaryOrderedHeartQuotientClass
    (f : ZetaAdmissibleFunction) :
    CompletedBoundaryOrderedHeartClass :=
  completedBoundaryOrderedHeartClass
    (completedFinitePartBoundaryOrderedHeartClass f)

/-- The completed ordered-heart quotient class represented by the positive square boundary
object. -/
def completedPositiveSquareBoundaryOrderedHeartQuotientClass
    (f : ZetaAdmissibleFunction) :
    CompletedBoundaryOrderedHeartClass :=
  completedBoundaryOrderedHeartClass
    (completedPositiveSquareBoundaryOrderedHeartClass f)

/-- The completed finite-part boundary quotient class is the positive square quotient class. -/
theorem completedFinitePartBoundaryOrderedHeartQuotientClass_eq_positiveSquare
    (f : ZetaAdmissibleFunction) :
    completedFinitePartBoundaryOrderedHeartQuotientClass f =
      completedPositiveSquareBoundaryOrderedHeartQuotientClass f := by
  exact completedBoundaryOrderedHeartClass_eq_of_GNSTomography
    (completedFinitePartBoundaryClass_GNSTomographicallyEquivalent_positiveSquare f)

/-- The finite-part boundary quotient scalar is the scalar of its representative. -/
theorem completedFinitePartBoundaryOrderedHeartQuotientScalar_eq_orderedHeartScalar
    (f : ZetaAdmissibleFunction) :
    completedBoundaryOrderedHeartClassScalar
        (completedFinitePartBoundaryOrderedHeartQuotientClass f) =
      completedOrderedHeartScalar
        (completedFinitePartBoundaryOrderedHeartClass f) := by
  rfl

/-- The positive square quotient scalar is the scalar of its representative. -/
theorem completedPositiveSquareBoundaryOrderedHeartQuotientScalar_eq_orderedHeartScalar
    (f : ZetaAdmissibleFunction) :
    completedBoundaryOrderedHeartClassScalar
        (completedPositiveSquareBoundaryOrderedHeartQuotientClass f) =
      completedOrderedHeartScalar
        (completedPositiveSquareBoundaryOrderedHeartClass f) := by
  rfl

/-- The completed finite-part boundary quotient scalar is the positive square quotient
scalar. -/
theorem completedFinitePartBoundaryOrderedHeartQuotientScalar_eq_positiveSquare
    (f : ZetaAdmissibleFunction) :
    completedBoundaryOrderedHeartClassScalar
        (completedFinitePartBoundaryOrderedHeartQuotientClass f) =
      completedBoundaryOrderedHeartClassScalar
        (completedPositiveSquareBoundaryOrderedHeartQuotientClass f) := by
  exact congrArg completedBoundaryOrderedHeartClassScalar
    (completedFinitePartBoundaryOrderedHeartQuotientClass_eq_positiveSquare f)

/-- The completed finite-part boundary quotient scalar is the completed GNS norm-square. -/
theorem completedFinitePartBoundaryOrderedHeartQuotientScalar_eq_GNSNormSq
    (f : ZetaAdmissibleFunction) :
    completedBoundaryOrderedHeartClassScalar
        (completedFinitePartBoundaryOrderedHeartQuotientClass f) =
      completedBoundaryGNSNormSq f := by
  exact
    (completedFinitePartBoundaryOrderedHeartQuotientScalar_eq_orderedHeartScalar
      f).trans
      (completedFinitePartBoundaryOrderedHeartScalar_eq_GNSNormSq f)

/-- The completed finite-part boundary quotient scalar is represented by the completed
renormalized positive defect-kernel channel. -/
theorem completedFinitePartBoundaryOrderedHeartQuotientScalar_eq_renormalizedDefectKernel
    (f : ZetaAdmissibleFunction) :
    completedBoundaryOrderedHeartClassScalar
        (completedFinitePartBoundaryOrderedHeartQuotientClass f) =
      completedRenormalizedDefectKernelBoundaryChannel f := by
  exact
    (completedFinitePartBoundaryOrderedHeartQuotientScalar_eq_orderedHeartScalar
      f).trans
      (completedFinitePartBoundaryOrderedHeartScalar_eq_renormalizedDefectKernel f)

/-- The finite-part boundary quotient scalar is nonnegative by descent to the positive GNS
square. -/
theorem completedFinitePartBoundaryOrderedHeartQuotientScalar_nonnegative
    (f : ZetaAdmissibleFunction) :
    0 ≤
      completedBoundaryOrderedHeartClassScalar
        (completedFinitePartBoundaryOrderedHeartQuotientClass f) := by
  have hgns : 0 ≤ completedBoundaryGNSNormSq f :=
    completedBoundaryGNSNormSq_nonnegative f
  exact Eq.subst
    (motive := fun x : ℝ => 0 ≤ x)
    (completedFinitePartBoundaryOrderedHeartQuotientScalar_eq_GNSNormSq f).symm
    hgns

/-- The completed analytic boundary realization class attached to an admissible seed.

This is the owner object for evaluating the contour boundary representative in the completed
ordered-heart quotient.  It is the finite-part boundary class after lower-weight absorption,
not the raw time-side scalar. -/
def completedAnalyticBoundaryRealizationClass
    (f : ZetaAdmissibleFunction) :
    CompletedBoundaryOrderedHeartClass :=
  completedFinitePartBoundaryOrderedHeartQuotientClass f

/-- The scalar induced by the completed analytic boundary realization. -/
def completedAnalyticBoundaryRealizationScalar
    (f : ZetaAdmissibleFunction) : ℝ :=
  completedBoundaryOrderedHeartClassScalar
    (completedAnalyticBoundaryRealizationClass f)

/-- The analytic boundary realization class is the completed finite-part ordered-heart
quotient class. -/
theorem completedAnalyticBoundaryRealizationClass_eq_finitePartQuotient
    (f : ZetaAdmissibleFunction) :
    completedAnalyticBoundaryRealizationClass f =
      completedFinitePartBoundaryOrderedHeartQuotientClass f := by
  rfl

/-- The analytic boundary realization scalar is the completed finite-part quotient scalar. -/
theorem completedAnalyticBoundaryRealizationScalar_eq_finitePartQuotientScalar
    (f : ZetaAdmissibleFunction) :
    completedAnalyticBoundaryRealizationScalar f =
      completedBoundaryOrderedHeartClassScalar
        (completedFinitePartBoundaryOrderedHeartQuotientClass f) := by
  rfl

/-- The analytic boundary realization scalar is the completed GNS norm-square. -/
theorem completedAnalyticBoundaryRealizationScalar_eq_GNSNormSq
    (f : ZetaAdmissibleFunction) :
    completedAnalyticBoundaryRealizationScalar f =
      completedBoundaryGNSNormSq f := by
  exact
    (completedAnalyticBoundaryRealizationScalar_eq_finitePartQuotientScalar
      f).trans
      (completedFinitePartBoundaryOrderedHeartQuotientScalar_eq_GNSNormSq f)

/-- The analytic boundary realization scalar is represented by the completed renormalized
positive defect-kernel channel. -/
theorem completedAnalyticBoundaryRealizationScalar_eq_renormalizedDefectKernel
    (f : ZetaAdmissibleFunction) :
    completedAnalyticBoundaryRealizationScalar f =
      completedRenormalizedDefectKernelBoundaryChannel f := by
  exact
    (completedAnalyticBoundaryRealizationScalar_eq_finitePartQuotientScalar
      f).trans
      (completedFinitePartBoundaryOrderedHeartQuotientScalar_eq_renormalizedDefectKernel f)

/-- The analytic boundary realization scalar is nonnegative by the completed GNS positive
cone. -/
theorem completedAnalyticBoundaryRealizationScalar_nonnegative
    (f : ZetaAdmissibleFunction) :
    0 ≤ completedAnalyticBoundaryRealizationScalar f := by
  have hquotient :
      0 ≤
        completedBoundaryOrderedHeartClassScalar
          (completedFinitePartBoundaryOrderedHeartQuotientClass f) :=
    completedFinitePartBoundaryOrderedHeartQuotientScalar_nonnegative f
  exact Eq.subst
    (motive := fun x : ℝ => 0 ≤ x)
    (completedAnalyticBoundaryRealizationScalar_eq_finitePartQuotientScalar f).symm
    hquotient

/-- The completed analytic boundary realization scalar is the ordered-heart scalar of the
finite-part boundary class. -/
theorem completedAnalyticBoundaryRealizationScalar_eq_finitePartOrderedHeartScalar
    (f : ZetaAdmissibleFunction) :
    completedAnalyticBoundaryRealizationScalar f =
      completedOrderedHeartScalar
        (completedFinitePartBoundaryOrderedHeartClass f) := by
  exact
    (completedAnalyticBoundaryRealizationScalar_eq_finitePartQuotientScalar
      f).trans
      (completedFinitePartBoundaryOrderedHeartQuotientScalar_eq_orderedHeartScalar f)

/-- The raw completed time-side boundary scalar.  This is the scalar represented by the
completed explicit-formula boundary channel before passing through the positive GNS
ordered-heart realization. -/
noncomputable def completedRawTimeBoundaryScalar
    (f : ZetaAdmissibleFunction) : ℝ :=
  Complex.re (completedBoundaryChannel (convolutionAutocorrelation f))

/-- Compatibility name for the raw symmetrized boundary scalar used in lower-weight descent.
The owner scalar is time-side; spectral packet comparisons are separate realization theorems. -/
noncomputable def completedSymmetrizedTwoFaceBoundaryScalar
    (f : ZetaAdmissibleFunction) : ℝ :=
  completedRawTimeBoundaryScalar f

/-- The positive defect-kernel completed boundary scalar.  This is the real part of the
positive GNS boundary form: prime is the defect-square kernel, while archimedean and
correction are the same Hermitian square channels. -/
noncomputable def completedPositiveDefectKernelBoundaryScalar
    (f : ZetaAdmissibleFunction) : ℝ :=
  Complex.re (zetaCompletedGNSPositiveBoundaryForm f)

/-- The completed renormalized defect-kernel channel is the positive GNS boundary scalar. -/
theorem completedRenormalizedDefectKernelBoundaryChannel_eq_positiveDefectKernelBoundaryScalar
    (f : ZetaAdmissibleFunction) :
    completedRenormalizedDefectKernelBoundaryChannel f =
      completedPositiveDefectKernelBoundaryScalar f := by
  have hrenormalized :
      completedRenormalizedDefectKernelBoundaryChannel f =
        completedBoundaryGNSNormSq f :=
    completedRenormalizedDefectKernelBoundaryChannel_eq_GNSNormSq f
  have hgns :
      completedBoundaryGNSNormSq f =
        completedBoundaryHermitianGNSScalar (completedBoundaryHilbertSource f) :=
    completedBoundaryGNSNormSq_eq_hermitianGNSScalar f
  have hpositive :
      completedBoundaryHermitianGNSScalar (completedBoundaryHilbertSource f) =
        completedPositiveDefectKernelBoundaryScalar f := by
    exact completedBoundaryHermitianGNSScalar_source_eq_positiveBoundaryScalar f
  exact hrenormalized.trans (hgns.trans hpositive)

/-- Archimedean raw-side transform bridge. -/
theorem archimedeanBoundaryChannel_convolutionAutocorrelation_eq_archimedeanConvolutionContribution
    (f : ZetaAdmissibleFunction) :
    archimedeanBoundaryChannel (convolutionAutocorrelation f) =
      zetaCompletedExplicitFormulaArchimedeanConvolutionContribution f := by
  unfold archimedeanBoundaryChannel
  exact
    zetaCompletedExplicitFormulaArchimedeanContribution_convolutionAutocorrelation_eq_paired_owner
      f

/-- Correction raw-side transform bridge. -/
theorem poleBoundaryChannel_convolutionAutocorrelation_eq_correctionConvolutionContribution
    (f : ZetaAdmissibleFunction) :
    poleBoundaryChannel (convolutionAutocorrelation f) =
      zetaCompletedExplicitFormulaCorrectionConvolutionContribution f := by
  unfold poleBoundaryChannel
  exact
    zetaCompletedExplicitFormulaCorrectionContribution_convolutionAutocorrelation_eq_owner
      f

/-- The raw completed time-side scalar is the real completed boundary channel. -/
theorem completedRawTimeBoundaryScalar_eq_completedBoundaryChannel_re
    (f : ZetaAdmissibleFunction) :
    completedRawTimeBoundaryScalar f =
      Complex.re (completedBoundaryChannel (convolutionAutocorrelation f)) := by
  rfl

/-- The completed finite-part channel is the raw completed time-side boundary scalar.

This is the raw analytic reconstruction part of lower-weight descent.  It deliberately does
not compare the time-side prime distribution with the finite paired spectral packet. -/
theorem completedFinitePartBoundaryChannel_eq_symmetrizedTwoFaceBoundaryScalar
    (f : ZetaAdmissibleFunction) :
    completedFinitePartBoundaryChannel f =
      completedSymmetrizedTwoFaceBoundaryScalar f := by
  have hfinite :
      completedFinitePartBoundaryChannel f =
        Complex.re (completedBoundaryChannel (convolutionAutocorrelation f)) :=
    completedFinitePartBoundaryChannel_eq_completedBoundaryChannel f
  have hraw :
      Complex.re (completedBoundaryChannel (convolutionAutocorrelation f)) =
        completedRawTimeBoundaryScalar f :=
    (completedRawTimeBoundaryScalar_eq_completedBoundaryChannel_re f).symm
  have halias :
      completedRawTimeBoundaryScalar f =
        completedSymmetrizedTwoFaceBoundaryScalar f := by
    unfold completedSymmetrizedTwoFaceBoundaryScalar
  exact hfinite.trans (hraw.trans halias)

/-- The finite-part time-pairing scalar is the absorbed positive-boundary precone scalar. -/
theorem completedFinitePartBoundaryTimePairingScalar_eq_positivePreconeScalar
    (f : ZetaAdmissibleFunction) :
    completedBoundaryTimePairingScalar
        (completedFinitePartBoundaryOrderedHeartClass f) =
      (completedPositiveBoundaryPreconeElement f).scalar := by
  have hclass :
      completedFinitePartBoundaryOrderedHeartClass f =
        completedPositiveBoundaryOrderedHeartClass f :=
    completedFinitePartBoundaryOrderedHeartClass_eq_positiveBoundary f
  have hpair :
      completedBoundaryTimePairingScalar
          (completedPositiveBoundaryOrderedHeartClass f) =
        (completedPositiveBoundaryPreconeElement f).scalar :=
    (completedPositiveBoundaryPreconeElement_scalar_eq_timePairingScalar f).symm
  exact (congrArg completedBoundaryTimePairingScalar hclass).trans hpair

/-- The finite absorption defect is lower-weight radical in the completed ordered-heart
quotient.

This is not a pointwise real-limit statement.  The diagonal-debt absorption face may be large
as a real finite-window correction; it is harmless because it is killed by the completed
lower-weight radical. -/
theorem completedPositiveBoundaryPreconeElement_absorptionDefect_lowerWeightRadical
    (f : ZetaAdmissibleFunction) :
    CompletedBoundaryHilbertSource.LowerWeightRadical
      (completedPositiveBoundaryAbsorptionDefectOrderedHeartClass f) := by
  exact completedPositiveBoundaryAbsorptionDefectOrderedHeartClass_lowerWeightRadical f

/-- The absorbed positive-boundary ordered-heart class: positive square class plus the
lower-weight absorption face. -/
def completedPositiveBoundaryAbsorbedOrderedHeartClass
    (f : ZetaAdmissibleFunction) : CompletedBoundaryHilbertSource :=
  completedPositiveBoundaryOrderedHeartClass f +
    completedPositiveBoundaryAbsorptionDefectOrderedHeartClass f

/-- The absorbed finite-window precone scalar is realized by the absorbed ordered-heart source.

This is the source-probe realization theorem for the scalar/window absorption certificate:
the scalar obtained as the limit of absorbed finite representatives is the time-pairing scalar
of the corresponding absorbed Hilbert source. -/
theorem completedPositiveBoundaryPreconeElement_scalar_eq_absorbedOrderedHeartTimePairingScalar
    (f : ZetaAdmissibleFunction) :
    (completedPositiveBoundaryPreconeElement f).scalar =
      completedBoundaryTimePairingScalar
        (completedPositiveBoundaryAbsorbedOrderedHeartClass f) := by
  have hpositive :
      (completedPositiveBoundaryPreconeElement f).scalar =
        completedBoundaryTimePairingScalar
          (completedPositiveBoundaryOrderedHeartClass f) :=
    completedPositiveBoundaryPreconeElement_scalar_eq_timePairingScalar f
  have habsorbed :
      completedBoundaryTimePairingScalar
          (completedPositiveBoundaryOrderedHeartClass f) =
        completedBoundaryTimePairingScalar
          (completedPositiveBoundaryAbsorbedOrderedHeartClass f) := by
    unfold completedPositiveBoundaryAbsorbedOrderedHeartClass
    unfold completedPositiveBoundaryAbsorptionDefectOrderedHeartClass
    exact
      (congrArg completedBoundaryTimePairingScalar
        (add_zero (completedPositiveBoundaryOrderedHeartClass f))).symm
  exact hpositive.trans habsorbed

/-- Radical absorption does not change the time-pairing scalar of the absorbed ordered-heart
source. -/
theorem completedPositiveBoundaryAbsorbedOrderedHeartTimePairingScalar_eq_positiveBoundaryTimePairingScalar
    (f : ZetaAdmissibleFunction)
    (habsorption :
      CompletedBoundaryHilbertSource.LowerWeightRadical
        (completedPositiveBoundaryAbsorptionDefectOrderedHeartClass f)) :
    completedBoundaryTimePairingScalar
        (completedPositiveBoundaryAbsorbedOrderedHeartClass f) =
      completedBoundaryTimePairingScalar
        (completedPositiveBoundaryOrderedHeartClass f) := by
  unfold completedPositiveBoundaryAbsorbedOrderedHeartClass
  exact completedBoundaryTimePairingScalar_eq_of_add_lowerWeightRadical
    completedBoundaryHilbertPairing_add_left
    completedBoundaryHilbertPairing_add_right
    (completedPositiveBoundaryOrderedHeartClass f)
    (completedPositiveBoundaryAbsorptionDefectOrderedHeartClass f)
    habsorption

/-- The positive-boundary time-pairing scalar is the raw completed time-side boundary scalar. -/
theorem completedPositiveBoundaryTimePairingScalar_eq_rawTimeBoundaryScalar
    (f : ZetaAdmissibleFunction) :
    completedBoundaryTimePairingScalar
        (completedPositiveBoundaryOrderedHeartClass f) =
      completedRawTimeBoundaryScalar f := by
  have hprecone :
      (completedPositiveBoundaryPreconeElement f).scalar =
        completedBoundaryTimePairingScalar
          (completedPositiveBoundaryOrderedHeartClass f) :=
    completedPositiveBoundaryPreconeElement_scalar_eq_timePairingScalar f
  have hscalar :
      (completedPositiveBoundaryPreconeElement f).scalar =
        completedRawTimeBoundaryScalar f := by
    exact (completedPositiveBoundaryPreconeElement_scalar_eq_boundaryChannel_re f).trans
      (completedRawTimeBoundaryScalar_eq_completedBoundaryChannel_re f).symm
  exact hprecone.symm.trans hscalar

/-- The positive ordered-heart scalar is the completed positive defect-kernel scalar. -/
theorem completedPositiveBoundaryOrderedHeartScalar_eq_positiveDefectKernelBoundaryScalar
    (f : ZetaAdmissibleFunction) :
    completedOrderedHeartScalar
        (completedPositiveBoundaryOrderedHeartClass f) =
      completedPositiveDefectKernelBoundaryScalar f := by
  unfold completedPositiveBoundaryOrderedHeartClass
  have hgns :
      completedOrderedHeartScalar (completedBoundaryHilbertSource f) =
        completedBoundaryGNSNormSq f := by
    exact (completedBoundaryGNSNormSq_eq_orderedHeartScalar f).symm
  have hrenormalized :
      completedBoundaryGNSNormSq f =
        completedRenormalizedDefectKernelBoundaryChannel f :=
    (completedRenormalizedDefectKernelBoundaryChannel_eq_GNSNormSq f).symm
  have hpositive :
      completedRenormalizedDefectKernelBoundaryChannel f =
        completedPositiveDefectKernelBoundaryScalar f :=
    completedRenormalizedDefectKernelBoundaryChannel_eq_positiveDefectKernelBoundaryScalar
      f
  exact hgns.trans (hrenormalized.trans hpositive)

/-- The raw time-side scalar is the completed finite-part boundary channel. -/
theorem completedRawTimeBoundaryScalar_eq_finitePartBoundaryChannel
    (f : ZetaAdmissibleFunction) :
    completedRawTimeBoundaryScalar f =
      completedFinitePartBoundaryChannel f := by
  have hraw :
      completedRawTimeBoundaryScalar f =
        Complex.re (completedBoundaryChannel (convolutionAutocorrelation f)) :=
    completedRawTimeBoundaryScalar_eq_completedBoundaryChannel_re f
  have hfinite :
      Complex.re (completedBoundaryChannel (convolutionAutocorrelation f)) =
        completedFinitePartBoundaryChannel f :=
    (completedFinitePartBoundaryChannel_eq_completedBoundaryChannel f).symm
  exact hraw.trans hfinite

/-- The finite positive renormalized boundary windows converge to the completed finite-part
boundary channel. -/
theorem finitePositiveRenormalizedBoundaryWindow_tendsto_completedFinitePartBoundaryChannel
    (f : ZetaAdmissibleFunction) :
    Tendsto
      (fun N : ℕ => finitePositiveRenormalizedBoundaryWindow N f)
      atTop
      (𝓝 (completedFinitePartBoundaryChannel f)) := by
  have hfinite :
      (fun N : ℕ => finitePositiveRenormalizedBoundaryWindow N f) =
        (fun N : ℕ => finitePartBoundaryWindow N f) := by
    funext N
    exact finitePositiveRenormalizedBoundaryWindow_eq_finitePartBoundaryWindow N f
  exact Eq.subst
    (motive := fun u : ℕ → ℝ =>
      Tendsto u atTop (𝓝 (completedFinitePartBoundaryChannel f)))
    hfinite.symm
    (finitePartBoundaryWindow_tendsto_completedFinitePartBoundaryChannel f)

/-- The scalar of the completed boundary weight stream is the completed finite-part boundary
channel. -/
theorem completedBoundaryWeightStream_scalar_eq_completedFinitePartBoundaryChannel
    (f : ZetaAdmissibleFunction) :
    (completedBoundaryWeightStream f).scalar =
      completedFinitePartBoundaryChannel f := by
  have hstream :
      (completedBoundaryWeightStream f).scalar =
        Complex.re (completedBoundaryChannel (convolutionAutocorrelation f)) :=
    completedBoundaryWeightStream_scalar_eq_boundaryChannel_re f
  have hfinite :
      Complex.re (completedBoundaryChannel (convolutionAutocorrelation f)) =
        completedFinitePartBoundaryChannel f :=
    (completedFinitePartBoundaryChannel_eq_completedBoundaryChannel f).symm
  exact hstream.trans hfinite

/-- The positive-cone completed boundary weight stream realizes in the completed ordered-heart
quotient scalar.

This is the stream-level lower-weight projection theorem: finite square representatives and
their lower-weight absorption certificates define the same completed scalar as the ordered
heart quotient class. -/
theorem completedBoundaryWeightStream_scalar_eq_orderedHeartQuotientScalar_by_positiveCone
    (f : ZetaAdmissibleFunction) :
    (completedBoundaryWeightStream f).scalar =
      completedBoundaryOrderedHeartClassScalar
        (completedFinitePartBoundaryOrderedHeartQuotientClass f) := by
  sorry

/-- The completed boundary weight stream scalar is represented by the completed renormalized
positive defect-kernel channel after projection to the ordered-heart quotient. -/
theorem completedBoundaryWeightStream_scalar_eq_renormalizedDefectKernel
    (f : ZetaAdmissibleFunction) :
    (completedBoundaryWeightStream f).scalar =
      completedRenormalizedDefectKernelBoundaryChannel f := by
  have hquotient :
      (completedBoundaryWeightStream f).scalar =
        completedBoundaryOrderedHeartClassScalar
          (completedFinitePartBoundaryOrderedHeartQuotientClass f) :=
    completedBoundaryWeightStream_scalar_eq_orderedHeartQuotientScalar_by_positiveCone
      f
  have hrenormalized :
      completedBoundaryOrderedHeartClassScalar
          (completedFinitePartBoundaryOrderedHeartQuotientClass f) =
        completedRenormalizedDefectKernelBoundaryChannel f :=
    completedFinitePartBoundaryOrderedHeartQuotientScalar_eq_renormalizedDefectKernel
      f
  exact hquotient.trans hrenormalized

/-- Owner channel-level lower-weight descent: the completed finite-part boundary channel is
represented by the completed renormalized positive defect-kernel channel.

This is the channel form of the lower-weight triangular transport theorem. -/
theorem completedFinitePartBoundaryChannel_eq_renormalizedDefectKernel_ownerDescent
    (f : ZetaAdmissibleFunction) :
    completedFinitePartBoundaryChannel f =
      completedRenormalizedDefectKernelBoundaryChannel f := by
  have hfinite :
      completedFinitePartBoundaryChannel f =
        (completedBoundaryWeightStream f).scalar :=
    (completedBoundaryWeightStream_scalar_eq_completedFinitePartBoundaryChannel f).symm
  have hstream :
      (completedBoundaryWeightStream f).scalar =
        completedRenormalizedDefectKernelBoundaryChannel f :=
    completedBoundaryWeightStream_scalar_eq_renormalizedDefectKernel f
  exact hfinite.trans hstream

/-- Owner scalar comparison between the raw completed time-side scalar and the positive
defect-kernel scalar.

This is the scalar normal form of completed ordered-heart quotient realization. -/
theorem completedRawTimeBoundaryScalar_eq_positiveDefectKernelBoundaryScalar_ownerRealization
    (f : ZetaAdmissibleFunction) :
    completedRawTimeBoundaryScalar f =
      completedPositiveDefectKernelBoundaryScalar f := by
  have hraw :
      completedRawTimeBoundaryScalar f =
        completedFinitePartBoundaryChannel f :=
    completedRawTimeBoundaryScalar_eq_finitePartBoundaryChannel f
  have hdescent :
      completedFinitePartBoundaryChannel f =
        completedRenormalizedDefectKernelBoundaryChannel f :=
    completedFinitePartBoundaryChannel_eq_renormalizedDefectKernel_ownerDescent f
  have hpositive :
      completedRenormalizedDefectKernelBoundaryChannel f =
        completedPositiveDefectKernelBoundaryScalar f :=
    completedRenormalizedDefectKernelBoundaryChannel_eq_positiveDefectKernelBoundaryScalar
      f
  exact hraw.trans (hdescent.trans hpositive)

/-- The positive-boundary representative's time-pairing scalar is its ordered-heart scalar.

This is the owner quotient-realization assertion for the positive GNS source: the reduced
time-side pairing and the completed ordered-heart GNS scalar agree on the canonical positive
boundary representative. -/
theorem completedPositiveBoundaryTimePairingScalar_eq_orderedHeartScalar_ownerRealization
    (f : ZetaAdmissibleFunction) :
    completedBoundaryTimePairingScalar
        (completedPositiveBoundaryOrderedHeartClass f) =
      completedOrderedHeartScalar
        (completedPositiveBoundaryOrderedHeartClass f) := by
  have htime :
      completedBoundaryTimePairingScalar
          (completedPositiveBoundaryOrderedHeartClass f) =
        completedRawTimeBoundaryScalar f :=
    completedPositiveBoundaryTimePairingScalar_eq_rawTimeBoundaryScalar f
  have hscalar :
      completedRawTimeBoundaryScalar f =
        completedPositiveDefectKernelBoundaryScalar f :=
    completedRawTimeBoundaryScalar_eq_positiveDefectKernelBoundaryScalar_ownerRealization
      f
  have hordered :
      completedPositiveDefectKernelBoundaryScalar f =
        completedOrderedHeartScalar
          (completedPositiveBoundaryOrderedHeartClass f) :=
    (completedPositiveBoundaryOrderedHeartScalar_eq_positiveDefectKernelBoundaryScalar
      f).symm
  exact htime.trans (hscalar.trans hordered)

/-- The finite-part representative's time-pairing scalar is its ordered-heart scalar.

This is the representative-level quotient-realization assertion.  It is intentionally placed
before the quotient-class scalar wrapper so downstream lower-weight transport cannot prove it
by circularly reusing the wrapper. -/
theorem completedFinitePartBoundaryTimePairingScalar_eq_orderedHeartScalar_by_quotientRealization
    (f : ZetaAdmissibleFunction) :
    completedBoundaryTimePairingScalar
        (completedFinitePartBoundaryOrderedHeartClass f) =
      completedOrderedHeartScalar
        (completedFinitePartBoundaryOrderedHeartClass f) := by
  have hclass :
      completedFinitePartBoundaryOrderedHeartClass f =
        completedPositiveBoundaryOrderedHeartClass f :=
    completedFinitePartBoundaryOrderedHeartClass_eq_positiveBoundary f
  have htime :
      completedBoundaryTimePairingScalar
          (completedFinitePartBoundaryOrderedHeartClass f) =
        completedBoundaryTimePairingScalar
          (completedPositiveBoundaryOrderedHeartClass f) :=
    congrArg completedBoundaryTimePairingScalar hclass
  have hpositive :
      completedBoundaryTimePairingScalar
          (completedPositiveBoundaryOrderedHeartClass f) =
        completedOrderedHeartScalar
          (completedPositiveBoundaryOrderedHeartClass f) :=
    completedPositiveBoundaryTimePairingScalar_eq_orderedHeartScalar_ownerRealization
      f
  have hordered :
      completedOrderedHeartScalar
          (completedPositiveBoundaryOrderedHeartClass f) =
        completedOrderedHeartScalar
          (completedFinitePartBoundaryOrderedHeartClass f) :=
    congrArg completedOrderedHeartScalar hclass.symm
  exact htime.trans (hpositive.trans hordered)

/-- The finite-part time-pairing scalar descends to the finite-part ordered-heart quotient
scalar. -/
theorem completedFinitePartBoundaryTimePairingScalar_eq_orderedHeartQuotientScalar_by_quotientRealization
    (f : ZetaAdmissibleFunction) :
    completedBoundaryTimePairingScalar
        (completedFinitePartBoundaryOrderedHeartClass f) =
      completedBoundaryOrderedHeartClassScalar
        (completedFinitePartBoundaryOrderedHeartQuotientClass f) := by
  have hrepresentative :
      completedBoundaryTimePairingScalar
          (completedFinitePartBoundaryOrderedHeartClass f) =
        completedOrderedHeartScalar
          (completedFinitePartBoundaryOrderedHeartClass f) :=
    completedFinitePartBoundaryTimePairingScalar_eq_orderedHeartScalar_by_quotientRealization
      f
  have hquotient :
      completedOrderedHeartScalar
          (completedFinitePartBoundaryOrderedHeartClass f) =
        completedBoundaryOrderedHeartClassScalar
          (completedFinitePartBoundaryOrderedHeartQuotientClass f) :=
    (completedFinitePartBoundaryOrderedHeartQuotientScalar_eq_orderedHeartScalar
      f).symm
  exact hrepresentative.trans hquotient

/-- The raw finite-part boundary scalar descends to the finite-part ordered-heart quotient
scalar.

This is the quotient-realization map for the finite-part representative: the real scalar
defined by the completed time-side boundary channel is the scalar induced by the completed
ordered-heart quotient class. -/
theorem completedFinitePartBoundaryChannel_eq_orderedHeartQuotientScalar_by_quotientRealization
    (f : ZetaAdmissibleFunction) :
    completedFinitePartBoundaryChannel f =
      completedBoundaryOrderedHeartClassScalar
        (completedFinitePartBoundaryOrderedHeartQuotientClass f) := by
  have htime :
      completedFinitePartBoundaryChannel f =
        completedBoundaryTimePairingScalar
          (completedFinitePartBoundaryOrderedHeartClass f) :=
    completedFinitePartBoundaryChannel_eq_timePairingScalar f
  have hquotient :
      completedBoundaryTimePairingScalar
          (completedFinitePartBoundaryOrderedHeartClass f) =
        completedBoundaryOrderedHeartClassScalar
          (completedFinitePartBoundaryOrderedHeartQuotientClass f) :=
    completedFinitePartBoundaryTimePairingScalar_eq_orderedHeartQuotientScalar_by_quotientRealization
      f
  exact htime.trans hquotient

/-- The finite-part ordered-heart quotient scalar is the positive defect-kernel scalar. -/
theorem completedFinitePartBoundaryOrderedHeartQuotientScalar_eq_positiveDefectKernelBoundaryScalar
    (f : ZetaAdmissibleFunction) :
    completedBoundaryOrderedHeartClassScalar
        (completedFinitePartBoundaryOrderedHeartQuotientClass f) =
      completedPositiveDefectKernelBoundaryScalar f := by
  have hquotient :
      completedBoundaryOrderedHeartClassScalar
          (completedFinitePartBoundaryOrderedHeartQuotientClass f) =
        completedRenormalizedDefectKernelBoundaryChannel f :=
    completedFinitePartBoundaryOrderedHeartQuotientScalar_eq_renormalizedDefectKernel
      f
  have hpositive :
      completedRenormalizedDefectKernelBoundaryChannel f =
        completedPositiveDefectKernelBoundaryScalar f :=
    completedRenormalizedDefectKernelBoundaryChannel_eq_positiveDefectKernelBoundaryScalar
      f
  exact hquotient.trans hpositive

/-- Quotient realization identifies the raw time-side scalar with the positive defect-kernel
ordered-heart scalar. -/
theorem completedRawTimeBoundaryScalar_eq_positiveDefectKernelBoundaryScalar_by_quotientRealization
    (f : ZetaAdmissibleFunction) :
    completedRawTimeBoundaryScalar f =
      completedPositiveDefectKernelBoundaryScalar f := by
  have hraw :
      completedRawTimeBoundaryScalar f =
        completedFinitePartBoundaryChannel f :=
    completedRawTimeBoundaryScalar_eq_finitePartBoundaryChannel f
  have hquotient :
      completedFinitePartBoundaryChannel f =
        completedBoundaryOrderedHeartClassScalar
          (completedFinitePartBoundaryOrderedHeartQuotientClass f) :=
    completedFinitePartBoundaryChannel_eq_orderedHeartQuotientScalar_by_quotientRealization
      f
  have hpositive :
      completedBoundaryOrderedHeartClassScalar
          (completedFinitePartBoundaryOrderedHeartQuotientClass f) =
        completedPositiveDefectKernelBoundaryScalar f :=
    completedFinitePartBoundaryOrderedHeartQuotientScalar_eq_positiveDefectKernelBoundaryScalar
      f
  exact hraw.trans (hquotient.trans hpositive)

/-- The positive-boundary time-pairing scalar is the positive ordered-heart GNS scalar after
lower-weight quotient realization. -/
theorem completedPositiveBoundaryTimePairingScalar_eq_orderedHeartScalar_by_quotientRealization
    (f : ZetaAdmissibleFunction) :
    completedBoundaryTimePairingScalar
        (completedPositiveBoundaryOrderedHeartClass f) =
      completedOrderedHeartScalar
        (completedPositiveBoundaryOrderedHeartClass f) := by
  exact completedPositiveBoundaryTimePairingScalar_eq_orderedHeartScalar_ownerRealization
    f

/-- Radical absorption identifies the absorbed positive-boundary precone scalar with the
positive ordered-heart scalar.

This is the genuine lower-weight transport theorem: the absorbed finite representatives
define the same completed scalar as the positive square class because their difference is the
lower-weight radical absorption face. -/
theorem completedPositiveBoundaryPreconeElement_scalar_eq_orderedHeartScalar_of_radicalAbsorption
    (f : ZetaAdmissibleFunction)
    (habsorption :
      CompletedBoundaryHilbertSource.LowerWeightRadical
        (completedPositiveBoundaryAbsorptionDefectOrderedHeartClass f)) :
    (completedPositiveBoundaryPreconeElement f).scalar =
      completedOrderedHeartScalar
        (completedPositiveBoundaryOrderedHeartClass f) := by
  have hsource :
      (completedPositiveBoundaryPreconeElement f).scalar =
        completedBoundaryTimePairingScalar
          (completedPositiveBoundaryAbsorbedOrderedHeartClass f) :=
    completedPositiveBoundaryPreconeElement_scalar_eq_absorbedOrderedHeartTimePairingScalar
      f
  have habsorbed :
      completedBoundaryTimePairingScalar
          (completedPositiveBoundaryAbsorbedOrderedHeartClass f) =
        completedBoundaryTimePairingScalar
          (completedPositiveBoundaryOrderedHeartClass f) :=
    completedPositiveBoundaryAbsorbedOrderedHeartTimePairingScalar_eq_positiveBoundaryTimePairingScalar
      f habsorption
  have hpositive :
      completedBoundaryTimePairingScalar
          (completedPositiveBoundaryOrderedHeartClass f) =
        completedOrderedHeartScalar
          (completedPositiveBoundaryOrderedHeartClass f) :=
    completedPositiveBoundaryTimePairingScalar_eq_orderedHeartScalar_by_quotientRealization
      f
  exact hsource.trans (habsorbed.trans hpositive)

/-- The absorbed positive-boundary precone scalar is the ordered-heart scalar of its class.

This is the limit-level lower-weight transport assertion: the finite absorbed representatives
converge to the same completed scalar as the positive GNS ordered-heart class.  The proof
belongs to the radical/nullspace transport from finite diagonal-debt absorption to the
completed ordered-heart quotient. -/
theorem completedPositiveBoundaryPreconeElement_scalar_eq_orderedHeartScalar_by_lowerWeightTriangularTransport
    (f : ZetaAdmissibleFunction) :
    (completedPositiveBoundaryPreconeElement f).scalar =
      completedOrderedHeartScalar
        (completedPositiveBoundaryOrderedHeartClass f) := by
  exact
    completedPositiveBoundaryPreconeElement_scalar_eq_orderedHeartScalar_of_radicalAbsorption
      f
      (completedPositiveBoundaryPreconeElement_absorptionDefect_lowerWeightRadical f)

/-- The finite-part class and positive-boundary class have the same ordered-heart scalar. -/
theorem completedFinitePartBoundaryOrderedHeartScalar_eq_positiveBoundary
    (f : ZetaAdmissibleFunction) :
    completedOrderedHeartScalar
        (completedPositiveBoundaryOrderedHeartClass f) =
      completedOrderedHeartScalar
        (completedFinitePartBoundaryOrderedHeartClass f) := by
  exact congrArg completedOrderedHeartScalar
    (completedFinitePartBoundaryOrderedHeartClass_eq_positiveBoundary f).symm

/-- Lower-weight triangular transport identifies the time-pairing scalar of the finite-part
representative with the ordered-heart GNS scalar of the same completed class.

This is the radical/nullspace payoff theorem.  The finite-part representative is evaluated by
the time-side completed pairing, while the ordered-heart scalar is evaluated by the positive
defect-kernel GNS pairing.  Diagonal-debt absorption says these are the same scalar after
quotienting by the lower-weight radical. -/
theorem completedFinitePartBoundaryTimePairingScalar_eq_orderedHeartScalar_by_lowerWeightTriangularTransport
    (f : ZetaAdmissibleFunction) :
    completedBoundaryTimePairingScalar
        (completedFinitePartBoundaryOrderedHeartClass f) =
      completedOrderedHeartScalar
        (completedFinitePartBoundaryOrderedHeartClass f) := by
  have htime :
      completedBoundaryTimePairingScalar
          (completedFinitePartBoundaryOrderedHeartClass f) =
        (completedPositiveBoundaryPreconeElement f).scalar :=
    completedFinitePartBoundaryTimePairingScalar_eq_positivePreconeScalar f
  have hprecone :
      (completedPositiveBoundaryPreconeElement f).scalar =
        completedOrderedHeartScalar
          (completedPositiveBoundaryOrderedHeartClass f) :=
    completedPositiveBoundaryPreconeElement_scalar_eq_orderedHeartScalar_by_lowerWeightTriangularTransport
      f
  have hclass :
      completedOrderedHeartScalar
          (completedPositiveBoundaryOrderedHeartClass f) =
        completedOrderedHeartScalar
          (completedFinitePartBoundaryOrderedHeartClass f) :=
    completedFinitePartBoundaryOrderedHeartScalar_eq_positiveBoundary f
  exact htime.trans (hprecone.trans hclass)

/-- Lower-weight triangular transport identifies the symmetrized two-face representative with
the positive defect-kernel representative in the completed ordered-heart scalar.

This is the exact radical-absorption step: the prime two-face cross term is not asserted to
be positive.  Instead, the completed ordered-heart transport replaces it by the positive
defect-square representative after the diagonal debt has been absorbed as lower-weight
radical data. -/
theorem completedSymmetrizedTwoFaceBoundaryScalar_eq_positiveDefectKernelBoundaryScalar
    (f : ZetaAdmissibleFunction) :
    completedSymmetrizedTwoFaceBoundaryScalar f =
      completedPositiveDefectKernelBoundaryScalar f := by
  have hsymm_to_finite :
      completedSymmetrizedTwoFaceBoundaryScalar f =
        completedFinitePartBoundaryChannel f :=
    (completedFinitePartBoundaryChannel_eq_symmetrizedTwoFaceBoundaryScalar f).symm
  have hfinite_to_time :
      completedFinitePartBoundaryChannel f =
        completedBoundaryTimePairingScalar
          (completedFinitePartBoundaryOrderedHeartClass f) :=
    completedFinitePartBoundaryChannel_eq_timePairingScalar f
  have htime_to_ordered :
      completedBoundaryTimePairingScalar
          (completedFinitePartBoundaryOrderedHeartClass f) =
        completedOrderedHeartScalar
          (completedFinitePartBoundaryOrderedHeartClass f) :=
    completedFinitePartBoundaryTimePairingScalar_eq_orderedHeartScalar_by_lowerWeightTriangularTransport
      f
  have hordered_to_renormalized :
      completedOrderedHeartScalar
          (completedFinitePartBoundaryOrderedHeartClass f) =
        completedRenormalizedDefectKernelBoundaryChannel f :=
    completedFinitePartBoundaryOrderedHeartScalar_eq_renormalizedDefectKernel f
  have hrenormalized_to_positive :
      completedRenormalizedDefectKernelBoundaryChannel f =
        completedPositiveDefectKernelBoundaryScalar f :=
    completedRenormalizedDefectKernelBoundaryChannel_eq_positiveDefectKernelBoundaryScalar
      f
  exact hsymm_to_finite.trans
    (hfinite_to_time.trans
      (htime_to_ordered.trans
        (hordered_to_renormalized.trans hrenormalized_to_positive)))

/-- Weight-triangular scalar descent identifies the raw completed finite-part channel with
the completed renormalized positive defect-kernel channel.

This is the finite-window payoff theorem: diagonal debt is absorbed as lower-weight radical
data, and the resulting completed scalar is represented by the positive defect-kernel
realization. -/
theorem completedFinitePartBoundaryChannel_eq_renormalizedDefectKernel_by_weightTriangularDescent
    (f : ZetaAdmissibleFunction) :
    completedFinitePartBoundaryChannel f =
      completedRenormalizedDefectKernelBoundaryChannel f := by
  exact completedFinitePartBoundaryChannel_eq_renormalizedDefectKernel_ownerDescent f

/-- The finite-part boundary class has the same completed time-pairing scalar and
ordered-heart Hermitian GNS scalar.

This is the owner reconstruction theorem for lower-weight descent: the time-side contour
representative is evaluated through the same completed ordered-heart class as the Hermitian
positive realization. -/
theorem completedFinitePartBoundaryTimePairingScalar_eq_orderedHeartScalar
    (f : ZetaAdmissibleFunction) :
    completedBoundaryTimePairingScalar
        (completedFinitePartBoundaryOrderedHeartClass f) =
      completedOrderedHeartScalar
        (completedFinitePartBoundaryOrderedHeartClass f) := by
  exact
    completedFinitePartBoundaryTimePairingScalar_eq_orderedHeartScalar_by_lowerWeightTriangularTransport
      f

/-- The finite-part boundary class has time-pairing scalar equal to the owner analytic
boundary realization scalar. -/
theorem completedFinitePartBoundaryTimePairingScalar_eq_completedAnalyticBoundaryRealizationScalar
    (f : ZetaAdmissibleFunction) :
    completedBoundaryTimePairingScalar
        (completedFinitePartBoundaryOrderedHeartClass f) =
      completedAnalyticBoundaryRealizationScalar f := by
  exact
    (completedFinitePartBoundaryTimePairingScalar_eq_orderedHeartScalar f).trans
      (completedAnalyticBoundaryRealizationScalar_eq_finitePartOrderedHeartScalar f).symm

/-- The raw completed finite-part boundary scalar descends to the owner completed analytic
boundary realization scalar.

This is the scalar form of lower-weight ordered-heart descent.  The left side is the raw
time-side finite-part representative, while the right side is the scalar induced by the
completed ordered-heart quotient class. -/
theorem completedFinitePartBoundaryChannel_eq_completedAnalyticBoundaryRealizationScalar
    (f : ZetaAdmissibleFunction) :
    completedFinitePartBoundaryChannel f =
      completedAnalyticBoundaryRealizationScalar f := by
  exact
    (completedFinitePartBoundaryChannel_eq_timePairingScalar f).trans
      (completedFinitePartBoundaryTimePairingScalar_eq_completedAnalyticBoundaryRealizationScalar
        f)

/-- The scalar of the completed positive-boundary precone element is the scalar of the
completed boundary weight stream. -/
theorem completedPositiveBoundaryPreconeElement_scalar_eq_weightStream_scalar
    (f : ZetaAdmissibleFunction) :
    (completedPositiveBoundaryPreconeElement f).scalar =
      (completedBoundaryWeightStream f).scalar := by
  rfl

/-- The completed positive-boundary precone element is represented by a completed boundary
weight stream in the positive cone. -/
theorem completedPositiveBoundaryPreconeElement_weightStream_mem_positiveCone
    (f : ZetaAdmissibleFunction) :
    CompletedBoundaryWeightStream.InPositiveCone
      (completedBoundaryWeightStream f) := by
  exact completedBoundaryWeightStream_mem_positiveCone f

/-- The positive representative is exactly the finite positive square-energy window. -/
theorem completedPositiveBoundaryPreconeElement_positiveRepresentative_eq_squareEnergyWindow
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    (completedPositiveBoundaryPreconeElement f).positiveRepresentative N =
      finitePositiveSquareEnergyWindow N f := by
  rfl

/-- The precone positive representative is the square representative of the finite boundary
weight object. -/
theorem completedPositiveBoundaryPreconeElement_positiveRepresentative_eq_weightSquare
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    (completedPositiveBoundaryPreconeElement f).positiveRepresentative N =
      FiniteBoundaryWeightObject.squareRepresentative
        (finiteBoundaryWeightObject N f) := by
  exact
    (completedPositiveBoundaryPreconeElement_positiveRepresentative_eq_squareEnergyWindow
      N f).trans
      (finiteBoundaryWeightObject_squareRepresentative_eq_squareEnergyWindow N f).symm

/-- The positive representative of the completed positive-boundary precone element is
pointwise nonnegative. -/
theorem completedPositiveBoundaryPreconeElement_positiveRepresentative_nonnegative
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    0 ≤ (completedPositiveBoundaryPreconeElement f).positiveRepresentative N := by
  exact (completedPositiveBoundaryPreconeElement f).positiveRepresentative_nonnegative N

/-- The absorbed representative of the completed positive-boundary precone element converges
to its scalar realization. -/
theorem completedPositiveBoundaryPreconeElement_absorbedRepresentative_tendsto_scalar
    (f : ZetaAdmissibleFunction) :
    Tendsto
      (completedPositiveBoundaryPreconeElement f).absorbedRepresentative
      atTop
      (𝓝 (completedPositiveBoundaryPreconeElement f).scalar) := by
  exact (completedPositiveBoundaryPreconeElement f).absorbedRepresentative_tendsto_scalar

/-- The absorbed representative is obtained from the positive square representative by adding
the named finite diagonal-debt absorption defect. -/
theorem completedPositiveBoundaryPreconeElement_absorbed_eq_positive_add_absorptionDefect
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    (completedPositiveBoundaryPreconeElement f).absorbedRepresentative N =
      (completedPositiveBoundaryPreconeElement f).positiveRepresentative N +
        (completedPositiveBoundaryPreconeElement f).absorptionDefect N := by
  have hdef :
      (completedPositiveBoundaryPreconeElement f).absorptionDefect N =
        (completedPositiveBoundaryPreconeElement f).absorbedRepresentative N -
          (completedPositiveBoundaryPreconeElement f).positiveRepresentative N :=
    (completedPositiveBoundaryPreconeElement f).absorptionDefect_eq N
  let A : ℝ := (completedPositiveBoundaryPreconeElement f).absorbedRepresentative N
  let Q : ℝ := (completedPositiveBoundaryPreconeElement f).positiveRepresentative N
  let E : ℝ := (completedPositiveBoundaryPreconeElement f).absorptionDefect N
  change A = Q + E
  have hE : E = A - Q := hdef
  calc
    A = Q + (A - Q) := by
      exact zetaBoundaryDebt_add_sub_cancel A Q
    _ = Q + E := by
      exact congrArg (fun x : ℝ => Q + x) hE.symm

/-- The absorbed representative is exactly the finite positive renormalized boundary window. -/
theorem completedPositiveBoundaryPreconeElement_absorbedRepresentative_eq_renormalizedWindow
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    (completedPositiveBoundaryPreconeElement f).absorbedRepresentative N =
      finitePositiveRenormalizedBoundaryWindow N f := by
  rfl

/-- The absorbed representative is exactly the finite-part boundary window. -/
theorem completedPositiveBoundaryPreconeElement_absorbedRepresentative_eq_finitePartWindow
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    (completedPositiveBoundaryPreconeElement f).absorbedRepresentative N =
      finitePartBoundaryWindow N f := by
  exact
    (completedPositiveBoundaryPreconeElement_absorbedRepresentative_eq_renormalizedWindow
      N f).trans
      (finitePositiveRenormalizedBoundaryWindow_eq_finitePartBoundaryWindow N f)

/-- The precone absorbed representative is the finite-part representative of the finite
boundary weight object. -/
theorem completedPositiveBoundaryPreconeElement_absorbedRepresentative_eq_weightFinitePart
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    (completedPositiveBoundaryPreconeElement f).absorbedRepresentative N =
      FiniteBoundaryWeightObject.finitePartRepresentative
        (finiteBoundaryWeightObject N f) := by
  exact
    (completedPositiveBoundaryPreconeElement_absorbedRepresentative_eq_finitePartWindow
      N f).trans
      (finiteBoundaryWeightObject_finitePartRepresentative_eq_finitePartBoundaryWindow
        N f).symm

/-- The precone absorption defect is the negative face of the finite diagonal debt. -/
theorem completedPositiveBoundaryPreconeElement_absorptionDefect_eq_neg_diagonalDebt
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    (completedPositiveBoundaryPreconeElement f).absorptionDefect N =
      - (finiteBoundaryWeightObject N f).diagonalDebt := by
  have hdefect :
      (completedPositiveBoundaryPreconeElement f).absorptionDefect N =
        finitePartDebtAbsorptionWindow N f :=
    completedPositiveBoundaryPreconeElement_absorptionDefect_eq_debtAbsorption N f
  have habs :
      finitePartDebtAbsorptionWindow N f =
        (finiteBoundaryWeightObject N f).debtAbsorption := by
    rfl
  have hneg :
      (finiteBoundaryWeightObject N f).debtAbsorption =
        - (finiteBoundaryWeightObject N f).diagonalDebt :=
    finiteBoundaryWeightObject_debtAbsorption_eq_neg_diagonalDebt N f
  exact hdefect.trans (habs.trans hneg)

/-- Completed precone-level weight-triangular transport: the positive square representative,
after adding the lower-weight absorption defect, is the finite-part weight representative. -/
theorem completedPositiveBoundaryPreconeElement_weightTriangularTransport
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    (completedPositiveBoundaryPreconeElement f).positiveRepresentative N +
        (completedPositiveBoundaryPreconeElement f).absorptionDefect N =
      FiniteBoundaryWeightObject.finitePartRepresentative
        (finiteBoundaryWeightObject N f) := by
  have habsorbed :
      (completedPositiveBoundaryPreconeElement f).absorbedRepresentative N =
        (completedPositiveBoundaryPreconeElement f).positiveRepresentative N +
          (completedPositiveBoundaryPreconeElement f).absorptionDefect N :=
    completedPositiveBoundaryPreconeElement_absorbed_eq_positive_add_absorptionDefect N f
  have hfinite :
      (completedPositiveBoundaryPreconeElement f).absorbedRepresentative N =
        FiniteBoundaryWeightObject.finitePartRepresentative
          (finiteBoundaryWeightObject N f) :=
    completedPositiveBoundaryPreconeElement_absorbedRepresentative_eq_weightFinitePart N f
  exact habsorbed.symm.trans hfinite

/-- Completed precone-level transport with the diagonal face written explicitly. -/
theorem completedPositiveBoundaryPreconeElement_positive_sub_diagonalDebt_eq_weightFinitePart
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    (completedPositiveBoundaryPreconeElement f).positiveRepresentative N -
        (finiteBoundaryWeightObject N f).diagonalDebt =
      FiniteBoundaryWeightObject.finitePartRepresentative
        (finiteBoundaryWeightObject N f) := by
  have hdefect :
      (completedPositiveBoundaryPreconeElement f).absorptionDefect N =
        - (finiteBoundaryWeightObject N f).diagonalDebt :=
    completedPositiveBoundaryPreconeElement_absorptionDefect_eq_neg_diagonalDebt N f
  calc
    (completedPositiveBoundaryPreconeElement f).positiveRepresentative N -
        (finiteBoundaryWeightObject N f).diagonalDebt =
        (completedPositiveBoundaryPreconeElement f).positiveRepresentative N +
          - (finiteBoundaryWeightObject N f).diagonalDebt := by
      exact sub_eq_add_neg
        ((completedPositiveBoundaryPreconeElement f).positiveRepresentative N)
        ((finiteBoundaryWeightObject N f).diagonalDebt)
    _ =
        (completedPositiveBoundaryPreconeElement f).positiveRepresentative N +
          (completedPositiveBoundaryPreconeElement f).absorptionDefect N := by
      exact congrArg
        (fun x : ℝ =>
          (completedPositiveBoundaryPreconeElement f).positiveRepresentative N + x)
        hdefect.symm
    _ =
        FiniteBoundaryWeightObject.finitePartRepresentative
          (finiteBoundaryWeightObject N f) := by
      exact completedPositiveBoundaryPreconeElement_weightTriangularTransport N f

/-- The absorbed representative is exactly the raw completed boundary window, because the
finite diagonal debt has been added and cancelled inside the finite-part normalization. -/
theorem completedPositiveBoundaryPreconeElement_absorbedRepresentative_eq_completedWindow
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    (completedPositiveBoundaryPreconeElement f).absorbedRepresentative N =
      completedBoundaryWindow N f := by
  exact
    (completedPositiveBoundaryPreconeElement_absorbedRepresentative_eq_finitePartWindow
      N f).trans
      (finitePartBoundaryWindow_eq_completedBoundaryWindow N f)

/-- The completed finite-part boundary form in the linear boundary normalization.  Positivity
is not owned by this scalar directly; it is compared to the positive Hermitian GNS scalar by
the ordered-heart transport layer. -/
noncomputable def completedFinitePartGNSBoundaryForm
    (f : ZetaAdmissibleFunction) : ℝ :=
  completedFinitePartBoundaryChannel f

/-- The completed finite-part boundary form realizes as the completed boundary scalar. -/
theorem completedFinitePartGNSBoundaryForm_eq_boundaryChannel_re
    (f : ZetaAdmissibleFunction) :
    completedFinitePartGNSBoundaryForm f =
      Complex.re (completedBoundaryChannel (convolutionAutocorrelation f)) := by
  unfold completedFinitePartGNSBoundaryForm
  exact completedFinitePartBoundaryChannel_eq_completedBoundaryChannel f

/-- The raw completed physical boundary windows converge to the completed boundary channel
after diagonal debt has been cancelled inside the finite-part normalization. -/
theorem completedBoundaryWindow_tendsto_boundaryChannel
    (f : ZetaAdmissibleFunction) :
    Tendsto
      (fun N : ℕ => completedBoundaryWindow N f)
      atTop
      (𝓝 (Complex.re (completedBoundaryChannel (convolutionAutocorrelation f)))) := by
  have hfinite :
      (fun N : ℕ => completedBoundaryWindow N f) =
        (fun N : ℕ => finitePartBoundaryWindow N f) := by
    funext N
    exact (finitePartBoundaryWindow_eq_completedBoundaryWindow N f).symm
  exact Eq.subst
    (motive := fun u : ℕ → ℝ =>
      Tendsto u atTop
        (𝓝 (Complex.re (completedBoundaryChannel (convolutionAutocorrelation f)))))
    hfinite.symm
    (finitePartBoundaryWindow_tendsto_boundaryChannel f)

/-- Compatibility wrapper for the explicit finite-window expression after the diagonal debt has
already been cancelled in the finite-part normalization. -/
theorem completedBoundaryWindow_tendsto
    (f : ZetaAdmissibleFunction) :
    Tendsto
      (fun N : ℕ => completedBoundaryWindow N f)
      atTop
      (𝓝 (Complex.re (completedBoundaryChannel (convolutionAutocorrelation f)))) := by
  exact completedBoundaryWindow_tendsto_boundaryChannel f

/-- The finite-window completed physical channel is nonnegative after adding its matching
prime diagonal debt. -/
theorem completedBoundaryWindow_add_diagonalDebt_nonnegative
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    0 ≤ completedBoundaryWindow N f + zetaPrimeDiagonalDebt N f := by
  exact completedCorrectedBoundaryWindow_nonnegative N f

/-- A real limit of an everywhere nonnegative sequence is nonnegative. -/
theorem nonnegative_of_tendsto_nonnegative
    {u : ℕ → ℝ} {x : ℝ}
    (hu : Tendsto u atTop (𝓝 x))
    (hnonneg : ∀ N : ℕ, 0 ≤ u N) :
    0 ≤ x := by
  have hclosed : IsClosed (Set.Ici (0 : ℝ)) :=
    isClosed_Ici
  have heventually : ∀ᶠ N in atTop, u N ∈ Set.Ici (0 : ℝ) :=
    Filter.Eventually.of_forall
      (fun N : ℕ => hnonneg N)
  exact hclosed.mem_of_tendsto hu heventually

/-- The completed boundary channel on an autocorrelation probe has real part represented by
the completed finite-part boundary channel. -/
theorem completedBoundaryChannel_convolutionAutocorrelation_re_eq_completedFinitePartBoundaryChannel
    (f : ZetaAdmissibleFunction) :
    Complex.re (completedBoundaryChannel (convolutionAutocorrelation f)) =
    completedFinitePartBoundaryChannel f := by
  exact (completedFinitePartBoundaryChannel_eq_completedBoundaryChannel f).symm

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
