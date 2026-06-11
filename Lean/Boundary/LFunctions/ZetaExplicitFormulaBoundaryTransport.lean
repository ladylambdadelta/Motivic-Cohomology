import Boundary.LFunctions.ZetaExplicitFormulaGeometry
import Boundary.LFunctions.ZetaZeroKreinGram
import Boundary.LFunctions.ZetaPacketComparison
import Boundary.LFunctions.ZetaHermitianPacket
import Boundary.LFunctions.ZetaCompletedBoundaryDescent

/-!
# Boundary explicit-formula transport

This file owns the proved transport between the explicit-formula boundary
package and the completed packet/boundary-defect package.

It deliberately does not prove the zero-side explicit formula

```lean
zetaCompletedZeroKreinGram f =
  ZetaAdmissibleFunction.zetaCompletedExplicitFormulaBoundarySum f
```

That equality is the analytic contour-shift theorem. The owner theorem for it
belongs to the completed explicit-formula assembly layer, after the residue,
decay, and vertical-decomposition inputs are available.
-/

namespace Boundary
namespace LFunctions

noncomputable section

namespace ZetaAdmissibleFunction

open Filter

/-- The completed explicit-formula boundary sum in signed real form. -/
noncomputable def zetaCompletedExplicitFormulaBoundarySum
    (f : ZetaAdmissibleFunction) : ℝ :=
  zetaCompletedBoundaryDefectGram f

/-- The completed boundary-defect Krein Gram in signed form. -/
noncomputable def zetaCompletedBoundaryDefectKreinGram
    (f : ZetaAdmissibleFunction) : ℝ :=
  zetaCompletedBoundaryDefectGram f

/-- The boundary-defect Krein notation is the boundary-defect Gram. -/
theorem zetaCompletedBoundaryDefectKreinGram_eq_boundaryDefectGram
    (f : ZetaAdmissibleFunction) :
    zetaCompletedBoundaryDefectKreinGram f =
      zetaCompletedBoundaryDefectGram f := by
  rfl

/-- The completed explicit-formula boundary sum is the boundary-defect Krein Gram. -/
theorem zetaCompletedExplicitFormulaBoundarySum_eq_boundaryDefectKreinGram
    (f : ZetaAdmissibleFunction) :
    zetaCompletedExplicitFormulaBoundarySum f =
      zetaCompletedBoundaryDefectKreinGram f := by
  rfl

/-- The completed explicit-formula boundary sum is the boundary-defect Gram. -/
theorem zetaCompletedExplicitFormulaBoundarySum_eq_boundaryDefectGram
    (f : ZetaAdmissibleFunction) :
    zetaCompletedExplicitFormulaBoundarySum f =
      zetaCompletedBoundaryDefectGram f := by
  rfl

/-- The boundary-defect Krein Gram is the centered completed packet norm square. -/
theorem zetaCompletedBoundaryDefectKreinGram_eq_completedPacketNormSq
    (f : ZetaAdmissibleFunction) :
    zetaCompletedBoundaryDefectKreinGram f =
      zetaCompletedPacketNormSq f 0 := by
  exact
    (zetaCompletedBoundaryDefectKreinGram_eq_boundaryDefectGram f).trans
      (zetaCompletedBoundaryDefectGram_eq_completedPacketNormSq f)

/-- The explicit-formula boundary sum is the centered completed packet norm square. -/
theorem zetaCompletedExplicitFormulaBoundarySum_eq_completedPacketNormSq
    (f : ZetaAdmissibleFunction) :
    zetaCompletedExplicitFormulaBoundarySum f =
      zetaCompletedPacketNormSq f 0 := by
  exact
    (zetaCompletedExplicitFormulaBoundarySum_eq_boundaryDefectKreinGram f).trans
      (zetaCompletedBoundaryDefectKreinGram_eq_completedPacketNormSq f)

/-- The centered completed packet norm square is the explicit-formula boundary sum. -/
theorem zetaCompletedPacketNormSq_eq_explicitFormulaBoundarySum
    (f : ZetaAdmissibleFunction) :
    zetaCompletedPacketNormSq f 0 =
      zetaCompletedExplicitFormulaBoundarySum f := by
  exact (zetaCompletedExplicitFormulaBoundarySum_eq_completedPacketNormSq f).symm

/-- The explicit-formula boundary sum is nonnegative through the packet norm square. -/
theorem zetaCompletedExplicitFormulaBoundarySum_nonnegative
    (f : ZetaAdmissibleFunction) :
    0 ≤ zetaCompletedExplicitFormulaBoundarySum f := by
  have hpacket : 0 ≤ zetaCompletedPacketNormSq f 0 :=
    zetaCompletedPacketNormSq_nonnegative f 0
  have hboundary :
      zetaCompletedExplicitFormulaBoundarySum f =
        zetaCompletedPacketNormSq f 0 :=
    zetaCompletedExplicitFormulaBoundarySum_eq_completedPacketNormSq f
  exact Eq.subst (motive := fun x : ℝ => 0 ≤ x) hboundary.symm hpacket

/-- The completed boundary-defect Krein Gram is nonnegative. -/
theorem zetaCompletedBoundaryDefectKreinGram_nonnegative
    (f : ZetaAdmissibleFunction) :
    0 ≤ zetaCompletedBoundaryDefectKreinGram f := by
  have hboundary : 0 ≤ zetaCompletedBoundaryDefectGram f :=
    zetaCompletedBoundaryDefectGram_nonnegative f
  have hkrein :
      zetaCompletedBoundaryDefectKreinGram f =
        zetaCompletedBoundaryDefectGram f :=
    zetaCompletedBoundaryDefectKreinGram_eq_boundaryDefectGram f
  exact Eq.subst (motive := fun x : ℝ => 0 ≤ x) hkrein.symm hboundary

/-- The geometry-layer analytic boundary sum is the analytic-core boundary sum. -/
theorem zetaCompletedExplicitFormulaBoundarySumAnalytic_eq_core
    (f : ZetaAdmissibleFunction) :
    zetaCompletedExplicitFormulaBoundarySumAnalytic f =
      zetaCompletedExplicitFormulaBoundarySumCore f := by
  exact
    (zetaCompletedExplicitFormulaBoundarySumAnalytic_eq f).trans
      (zetaCompletedExplicitFormulaBoundarySumCore_eq f).symm

/-- The real part of the analytic-core boundary expression. This is the linear explicit-formula
boundary functional before it is compared with the Krein/Gram packet normalization. -/
noncomputable def zetaCompletedExplicitFormulaBoundaryLinearRealSum
    (f : ZetaAdmissibleFunction) : ℝ :=
  Complex.re (zetaCompletedExplicitFormulaBoundarySumCore f)

/-- The analytic boundary sum has the same real part as the analytic-core boundary sum. -/
theorem zetaCompletedExplicitFormulaBoundaryLinearRealSum_eq_analytic
    (f : ZetaAdmissibleFunction) :
    zetaCompletedExplicitFormulaBoundaryLinearRealSum f =
      Complex.re (zetaCompletedExplicitFormulaBoundarySumAnalytic f) := by
  exact congrArg Complex.re (zetaCompletedExplicitFormulaBoundarySumAnalytic_eq_core f).symm

/-- The real linear boundary sum unfolds to the real parts of the prime, archimedean, and
correction contributions. -/
theorem zetaCompletedExplicitFormulaBoundaryLinearRealSum_eq_components
    (f : ZetaAdmissibleFunction) :
    zetaCompletedExplicitFormulaBoundaryLinearRealSum f =
      Complex.re (zetaCompletedExplicitFormulaPrimeContribution f) +
        Complex.re (zetaCompletedExplicitFormulaArchimedeanContribution f) +
        Complex.re (zetaCompletedExplicitFormulaCorrectionContribution f) := by
  exact congrArg Complex.re (zetaCompletedExplicitFormulaBoundarySumCore_eq f)

/-- The Krein/Gram boundary expression attached to the explicit-formula packets. -/
noncomputable def zetaCompletedExplicitFormulaBoundaryKreinSum
    (f : ZetaAdmissibleFunction) : ℝ :=
  zetaCompletedBoundaryDefectGram f

/-- The Krein boundary sum is the signed real boundary sum used downstream. -/
theorem zetaCompletedExplicitFormulaBoundaryKreinSum_eq_realBoundarySum
    (f : ZetaAdmissibleFunction) :
    zetaCompletedExplicitFormulaBoundaryKreinSum f =
      zetaCompletedExplicitFormulaBoundarySum f := by
  rfl

/-- The Krein boundary sum is the completed packet norm square. -/
theorem zetaCompletedExplicitFormulaBoundaryKreinSum_eq_completedPacketNormSq
    (f : ZetaAdmissibleFunction) :
    zetaCompletedExplicitFormulaBoundaryKreinSum f =
      zetaCompletedPacketNormSq f 0 := by
  exact zetaCompletedBoundaryDefectGram_eq_completedPacketNormSq f

/-- The convolution-autocorrelation boundary Krein sum is the real part of the completed
boundary channel on the convolution autocorrelation probe.  Positivity is supplied by the
completed-square descent theorem, not by collapsing paired spectral coordinates. -/
noncomputable def zetaCompletedExplicitFormulaConvolutionAutocorrelationBoundaryKreinSum
    (f : ZetaAdmissibleFunction) : ℝ :=
  Complex.re (completedBoundaryChannel (ZetaAdmissibleFunction.convolutionAutocorrelation f))

/-- Historical name for the convolution-autocorrelation boundary Krein sum. -/
abbrev zetaCompletedExplicitFormulaAutocorrelationBoundaryKreinSum
    (f : ZetaAdmissibleFunction) : ℝ :=
  zetaCompletedExplicitFormulaConvolutionAutocorrelationBoundaryKreinSum f

/-- The convolution-autocorrelation boundary real form carries the completed positive-class
certificate constructed by finite defect-square descent. -/
def zetaCompletedExplicitFormulaConvolutionAutocorrelationBoundaryPositiveClass
    (f : ZetaAdmissibleFunction) : CompletedPositiveBoundaryPreconeElement :=
  completedPositiveBoundaryPreconeElement f

/-- Historical name for the convolution-autocorrelation completed positive-class certificate. -/
abbrev zetaCompletedExplicitFormulaAutocorrelationBoundaryPositiveClass
    (f : ZetaAdmissibleFunction) : CompletedPositiveBoundaryPreconeElement :=
  zetaCompletedExplicitFormulaConvolutionAutocorrelationBoundaryPositiveClass f

/-- The positive representative in the convolution-autocorrelation boundary class is
pointwise nonnegative. -/
theorem zetaCompletedExplicitFormulaAutocorrelationBoundaryPositiveClass_nonnegative
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    0 ≤
      (zetaCompletedExplicitFormulaAutocorrelationBoundaryPositiveClass f).positiveRepresentative
        N := by
  exact completedPositiveBoundaryPreconeElement_positiveRepresentative_nonnegative N f

/-- The absorbed representative in the convolution-autocorrelation boundary class realizes to
the boundary Krein scalar. -/
theorem zetaCompletedExplicitFormulaAutocorrelationBoundaryPositiveClass_tendsto
    (f : ZetaAdmissibleFunction) :
    Tendsto
      (zetaCompletedExplicitFormulaAutocorrelationBoundaryPositiveClass f).absorbedRepresentative
      atTop
      (𝓝 (zetaCompletedExplicitFormulaAutocorrelationBoundaryKreinSum f)) := by
  exact completedPositiveBoundaryPreconeElement_absorbedRepresentative_tendsto_scalar f

/-- A complex number is a real scalar once its real part is the scalar and its imaginary part
vanishes. -/
theorem complex_eq_of_re_eq_of_im_eq_zero
    (z : ℂ) (r : ℝ)
    (hre : Complex.re z = r)
    (him : Complex.im z = 0) :
    z = (r : ℂ) := by
  exact Complex.ext hre (him.trans (Complex.ofReal_im r).symm)

/-- Prime-channel holography: the prime explicit-formula functional evaluated on the
convolution autocorrelation kernel is the two-face/GNS prime matrix coefficient. -/
theorem zetaCompletedExplicitFormulaPrimeChannel_holographic
    (f : ZetaAdmissibleFunction)
    (hself : zetaCompletedExplicitFormulaPrimeConvolutionContributionTwoFace f) :
    Complex.re (zetaCompletedExplicitFormulaPrimeConvolutionContribution f) =
      Complex.re (zetaPrimeTwoFaceGNSMatrixCoefficient f) := by
  exact zetaCompletedExplicitFormulaPrimeConvolutionChannel_holographic_twoFace f hself

/-- The prime linear boundary functional on the convolution autocorrelation kernel is its
two-face/GNS prime packet contribution. -/
theorem zetaCompletedExplicitFormulaPrimeConvolutionLinearReal_eq_twoFaceMatrixCoefficient
    (f : ZetaAdmissibleFunction)
    (hself : zetaCompletedExplicitFormulaPrimeConvolutionContributionTwoFace f) :
    Complex.re (zetaCompletedExplicitFormulaPrimeConvolutionContribution f) =
      Complex.re (zetaPrimeTwoFaceGNSMatrixCoefficient f) := by
  exact zetaCompletedExplicitFormulaPrimeChannel_holographic f hself

/-- Historical name for prime convolution-channel holography. -/
theorem zetaCompletedExplicitFormulaPrimeLinearReal_autocorrelation_eq_twoFaceMatrixCoefficient
    (f : ZetaAdmissibleFunction)
    (hself : zetaCompletedExplicitFormulaPrimeConvolutionContributionTwoFace f) :
    Complex.re (zetaCompletedExplicitFormulaPrimeConvolutionContribution f) =
      Complex.re (zetaPrimeTwoFaceGNSMatrixCoefficient f) := by
  exact zetaCompletedExplicitFormulaPrimeConvolutionLinearReal_eq_twoFaceMatrixCoefficient f hself

/-- Archimedean-channel holography: the archimedean explicit-formula functional evaluated
on the convolution autocorrelation kernel is the Hermitian archimedean packet Gram under the
self-dual specialization. -/
theorem zetaCompletedExplicitFormulaArchimedeanChannel_holographic
    (f : ZetaAdmissibleFunction)
    (hself : zetaCompletedExplicitFormulaArchimedeanConvolutionContributionSelfDual f) :
    Complex.re (zetaCompletedExplicitFormulaArchimedeanConvolutionContribution f) =
      ZetaHermitianPacketEnsemble.archimedeanPacketGram
        (zetaCompletedHermitianBoundaryDefect f) := by
  exact zetaCompletedExplicitFormulaArchimedeanConvolutionChannel_holographic_of_selfDual f hself

/-- The archimedean linear boundary functional on the convolution autocorrelation kernel is its
Hermitian archimedean packet contribution under the self-dual specialization. -/
theorem zetaCompletedExplicitFormulaArchimedeanConvolutionLinearReal_eq_archimedeanPacketGram
    (f : ZetaAdmissibleFunction)
    (hself : zetaCompletedExplicitFormulaArchimedeanConvolutionContributionSelfDual f) :
    Complex.re (zetaCompletedExplicitFormulaArchimedeanConvolutionContribution f) =
      ZetaHermitianPacketEnsemble.archimedeanPacketGram
        (zetaCompletedHermitianBoundaryDefect f) := by
  exact zetaCompletedExplicitFormulaArchimedeanChannel_holographic f hself

/-- Historical name for archimedean convolution-channel holography. -/
theorem zetaCompletedExplicitFormulaArchimedeanLinearReal_autocorrelation_eq_archimedeanPacketGram
    (f : ZetaAdmissibleFunction)
    (hself : zetaCompletedExplicitFormulaArchimedeanConvolutionContributionSelfDual f) :
    Complex.re (zetaCompletedExplicitFormulaArchimedeanConvolutionContribution f) =
      ZetaHermitianPacketEnsemble.archimedeanPacketGram
        (zetaCompletedHermitianBoundaryDefect f) := by
  exact zetaCompletedExplicitFormulaArchimedeanConvolutionLinearReal_eq_archimedeanPacketGram
    f hself

/-- Correction-channel holography: the correction explicit-formula functional evaluated on the
convolution autocorrelation kernel is the Hermitian correction packet Gram. -/
theorem zetaCompletedExplicitFormulaCorrectionChannel_holographic
    (f : ZetaAdmissibleFunction) :
    Complex.re (zetaCompletedExplicitFormulaCorrectionConvolutionContribution f) =
      ZetaHermitianPacketEnsemble.correctionPacketGram
        (zetaCompletedHermitianBoundaryDefect f) := by
  exact zetaCompletedExplicitFormulaCorrectionConvolutionChannel_holographic f

/-- The correction linear boundary functional on the convolution autocorrelation kernel is its
Hermitian correction packet contribution. -/
theorem zetaCompletedExplicitFormulaCorrectionConvolutionLinearReal_eq_correctionPacketGram
    (f : ZetaAdmissibleFunction) :
    Complex.re (zetaCompletedExplicitFormulaCorrectionConvolutionContribution f) =
      ZetaHermitianPacketEnsemble.correctionPacketGram
        (zetaCompletedHermitianBoundaryDefect f) := by
  exact zetaCompletedExplicitFormulaCorrectionChannel_holographic f

/-- Historical name for correction convolution-channel holography. -/
theorem zetaCompletedExplicitFormulaCorrectionLinearReal_autocorrelation_eq_correctionPacketGram
    (f : ZetaAdmissibleFunction) :
    Complex.re (zetaCompletedExplicitFormulaCorrectionConvolutionContribution f) =
      ZetaHermitianPacketEnsemble.correctionPacketGram
        (zetaCompletedHermitianBoundaryDefect f) := by
  exact zetaCompletedExplicitFormulaCorrectionConvolutionLinearReal_eq_correctionPacketGram f

/-- The convolution-autocorrelation boundary functional in real channel form. -/
noncomputable def zetaCompletedExplicitFormulaConvolutionBoundaryLinearRealSum
    (f : ZetaAdmissibleFunction) : ℝ :=
  Complex.re (zetaCompletedExplicitFormulaPrimeConvolutionContribution f) +
    Complex.re (zetaCompletedExplicitFormulaArchimedeanConvolutionContribution f) +
    Complex.re (zetaCompletedExplicitFormulaCorrectionConvolutionContribution f)

/-- The convolution-autocorrelation boundary functional in complex channel form. -/
noncomputable def zetaCompletedExplicitFormulaConvolutionBoundarySumAnalytic
    (f : ZetaAdmissibleFunction) : ℂ :=
  zetaCompletedExplicitFormulaPrimeConvolutionContribution f +
    zetaCompletedExplicitFormulaArchimedeanConvolutionContribution f +
    zetaCompletedExplicitFormulaCorrectionConvolutionContribution f

/-- The real part of the convolution boundary sum is the real channel sum. -/
theorem zetaCompletedExplicitFormulaConvolutionBoundarySumAnalytic_re
    (f : ZetaAdmissibleFunction) :
    Complex.re (zetaCompletedExplicitFormulaConvolutionBoundarySumAnalytic f) =
      zetaCompletedExplicitFormulaConvolutionBoundaryLinearRealSum f := by
  unfold zetaCompletedExplicitFormulaConvolutionBoundarySumAnalytic
  unfold zetaCompletedExplicitFormulaConvolutionBoundaryLinearRealSum
  calc
    Complex.re
        (zetaCompletedExplicitFormulaPrimeConvolutionContribution f +
          zetaCompletedExplicitFormulaArchimedeanConvolutionContribution f +
          zetaCompletedExplicitFormulaCorrectionConvolutionContribution f) =
        Complex.re
            (zetaCompletedExplicitFormulaPrimeConvolutionContribution f +
              zetaCompletedExplicitFormulaArchimedeanConvolutionContribution f) +
          Complex.re (zetaCompletedExplicitFormulaCorrectionConvolutionContribution f) :=
      Complex.add_re
        (zetaCompletedExplicitFormulaPrimeConvolutionContribution f +
          zetaCompletedExplicitFormulaArchimedeanConvolutionContribution f)
        (zetaCompletedExplicitFormulaCorrectionConvolutionContribution f)
    _ =
        (Complex.re (zetaCompletedExplicitFormulaPrimeConvolutionContribution f) +
          Complex.re (zetaCompletedExplicitFormulaArchimedeanConvolutionContribution f)) +
          Complex.re (zetaCompletedExplicitFormulaCorrectionConvolutionContribution f) := by
      exact congrArg
        (fun x : ℝ =>
          x + Complex.re (zetaCompletedExplicitFormulaCorrectionConvolutionContribution f))
        (Complex.add_re
          (zetaCompletedExplicitFormulaPrimeConvolutionContribution f)
          (zetaCompletedExplicitFormulaArchimedeanConvolutionContribution f))
    _ =
        Complex.re (zetaCompletedExplicitFormulaPrimeConvolutionContribution f) +
          Complex.re (zetaCompletedExplicitFormulaArchimedeanConvolutionContribution f) +
          Complex.re (zetaCompletedExplicitFormulaCorrectionConvolutionContribution f) := by
      rfl

/-- The paired convolution boundary form. -/
noncomputable def zetaCompletedExplicitFormulaConvolutionBoundaryPairedForm
    (f : ZetaAdmissibleFunction) : ℂ :=
  zetaCompletedPairedSpectralBoundaryForm f

/-- Historical name for the real part of the paired spectral convolution boundary form.
This is not the public completed time-side Krein scalar. -/
noncomputable def zetaCompletedExplicitFormulaConvolutionBoundaryKreinSum
    (f : ZetaAdmissibleFunction) : ℝ :=
  Complex.re (zetaCompletedExplicitFormulaConvolutionBoundaryPairedForm f)

/-- The real paired-spectral convolution boundary functional agrees with the real part of the
paired spectral boundary form. -/
theorem zetaCompletedExplicitFormulaConvolutionBoundaryLinearRealSum_eq_seedKreinSum
    (f : ZetaAdmissibleFunction) :
    zetaCompletedExplicitFormulaConvolutionBoundaryLinearRealSum f =
      zetaCompletedExplicitFormulaConvolutionBoundaryKreinSum f := by
  have hsum :
      zetaCompletedPairedSpectralBoundaryForm f =
        zetaCompletedExplicitFormulaPrimeConvolutionContribution f +
          zetaCompletedExplicitFormulaArchimedeanConvolutionContribution f +
          zetaCompletedExplicitFormulaCorrectionConvolutionContribution f :=
    zetaCompletedPairedSpectralBoundaryForm_eq_convolutionContributions f
  have hre :
      Complex.re
          (zetaCompletedExplicitFormulaPrimeConvolutionContribution f +
            zetaCompletedExplicitFormulaArchimedeanConvolutionContribution f +
            zetaCompletedExplicitFormulaCorrectionConvolutionContribution f) =
        Complex.re (zetaCompletedPairedSpectralBoundaryForm f) :=
    congrArg Complex.re hsum.symm
  have hleft :
      Complex.re (zetaCompletedExplicitFormulaConvolutionBoundarySumAnalytic f) =
        zetaCompletedExplicitFormulaConvolutionBoundaryLinearRealSum f :=
    zetaCompletedExplicitFormulaConvolutionBoundarySumAnalytic_re f
  unfold zetaCompletedExplicitFormulaConvolutionBoundaryKreinSum
  unfold zetaCompletedExplicitFormulaConvolutionBoundaryPairedForm
  exact hleft.symm.trans hre

/-- Historical name for the real convolution boundary assembly theorem. -/
theorem zetaCompletedExplicitFormulaBoundaryLinearRealSum_autocorrelation_eq_seedKreinSum
    (f : ZetaAdmissibleFunction) :
    zetaCompletedExplicitFormulaConvolutionBoundaryLinearRealSum f =
      zetaCompletedExplicitFormulaConvolutionBoundaryKreinSum f := by
  exact zetaCompletedExplicitFormulaConvolutionBoundaryLinearRealSum_eq_seedKreinSum f

/-- The convolution boundary sum is real. -/
theorem zetaCompletedExplicitFormulaConvolutionBoundarySumAnalytic_im_eq_zero
    (f : ZetaAdmissibleFunction) :
    Complex.im (zetaCompletedExplicitFormulaConvolutionBoundarySumAnalytic f) = 0 := by
  have hsum :
      zetaCompletedPairedSpectralBoundaryForm f =
        zetaCompletedExplicitFormulaPrimeConvolutionContribution f +
          zetaCompletedExplicitFormulaArchimedeanConvolutionContribution f +
          zetaCompletedExplicitFormulaCorrectionConvolutionContribution f :=
    zetaCompletedPairedSpectralBoundaryForm_eq_convolutionContributions f
  have him :
      Complex.im
          (zetaCompletedExplicitFormulaPrimeConvolutionContribution f +
            zetaCompletedExplicitFormulaArchimedeanConvolutionContribution f +
            zetaCompletedExplicitFormulaCorrectionConvolutionContribution f) =
        Complex.im (zetaCompletedPairedSpectralBoundaryForm f) :=
    congrArg Complex.im hsum.symm
  unfold zetaCompletedExplicitFormulaConvolutionBoundarySumAnalytic
  exact him.trans (zetaCompletedPairedSpectralBoundaryForm_im_eq_zero f)

/-- The complex convolution boundary sum agrees with the paired spectral boundary form. -/
theorem zetaCompletedExplicitFormulaConvolutionBoundarySumAnalytic_eq_pairedForm
    (f : ZetaAdmissibleFunction) :
    zetaCompletedExplicitFormulaConvolutionBoundarySumAnalytic f =
      zetaCompletedExplicitFormulaConvolutionBoundaryPairedForm f := by
  unfold zetaCompletedExplicitFormulaConvolutionBoundarySumAnalytic
  unfold zetaCompletedExplicitFormulaConvolutionBoundaryPairedForm
  exact (zetaCompletedPairedSpectralBoundaryForm_eq_convolutionContributions f).symm

/-- The real two-face prime presentation is the realized prime GNS channel. -/
theorem zetaRealPrimePresentation_eq_realizedPrimeGram
    (f : ZetaAdmissibleFunction) :
    (∑ ℓ in zetaCompletedExplicitFormulaPrimeSupport,
        (zetaCompletedExplicitFormulaPrimeWeight ℓ.1 ℓ.2 : ℂ) *
          ((zetaCompletedExplicitFormulaPhi f (zetaPrimePacketCenter ℓ.1 ℓ.2) *
              star
                (zetaCompletedExplicitFormulaPhi f
                  (-(zetaPrimePacketCenter ℓ.1 ℓ.2 : ℂ)))) +
            star
              (zetaCompletedExplicitFormulaPhi f (zetaPrimePacketCenter ℓ.1 ℓ.2) *
                star
                  (zetaCompletedExplicitFormulaPhi f
                    (-(zetaPrimePacketCenter ℓ.1 ℓ.2 : ℂ)))))) =
      zetaCompletedPrimeBoundaryRealizedGram f := by
  unfold zetaCompletedPrimeBoundaryRealizedGram
  unfold zetaCompletedPrimeBoundaryRealizedCoordinateGram
  refine Finset.sum_congr rfl ?_
  intro ℓ hℓ
  have hface :
      zetaCompletedAutocorrelationPrimePositiveFace ℓ.1 ℓ.2
          (zetaCompletedAutocorrelationProbe f) =
        zetaCompletedPrimeHermitianSeedAmplitude ℓ.1 ℓ.2 f *
          star (zetaCompletedPrimeHermitianNegativeSeedAmplitude ℓ.1 ℓ.2 f) := by
    unfold zetaCompletedAutocorrelationPrimePositiveFace
    unfold zetaCompletedAutocorrelationProbe
    unfold ZetaCompletedAutocorrelationProbe.toAdmissible
    unfold zetaCompletedPrimeHermitianSeedAmplitude
    unfold zetaCompletedPrimeHermitianNegativeSeedAmplitude
    exact zetaCompletedExplicitFormulaPhi_convolutionAutocorrelation_real_pair
      f (zetaPrimePacketCenter ℓ.1 ℓ.2)
  calc
    (zetaCompletedExplicitFormulaPrimeWeight ℓ.1 ℓ.2 : ℂ) *
        ((zetaCompletedExplicitFormulaPhi f (zetaPrimePacketCenter ℓ.1 ℓ.2) *
            star
              (zetaCompletedExplicitFormulaPhi f
                (-(zetaPrimePacketCenter ℓ.1 ℓ.2 : ℂ)))) +
          star
            (zetaCompletedExplicitFormulaPhi f (zetaPrimePacketCenter ℓ.1 ℓ.2) *
              star
                (zetaCompletedExplicitFormulaPhi f
                  (-(zetaPrimePacketCenter ℓ.1 ℓ.2 : ℂ))))) =
        (zetaCompletedExplicitFormulaPrimeWeight ℓ.1 ℓ.2 : ℂ) *
          ((zetaCompletedPrimeHermitianSeedAmplitude ℓ.1 ℓ.2 f *
              star (zetaCompletedPrimeHermitianNegativeSeedAmplitude ℓ.1 ℓ.2 f)) +
            star
              (zetaCompletedPrimeHermitianSeedAmplitude ℓ.1 ℓ.2 f *
                star (zetaCompletedPrimeHermitianNegativeSeedAmplitude ℓ.1 ℓ.2 f))) := by
      unfold zetaCompletedPrimeHermitianSeedAmplitude
      unfold zetaCompletedPrimeHermitianNegativeSeedAmplitude
      rfl
    _ =
        (zetaCompletedExplicitFormulaPrimeWeight ℓ.1 ℓ.2 : ℂ) *
          (zetaCompletedAutocorrelationPrimePositiveFace ℓ.1 ℓ.2
              (zetaCompletedAutocorrelationProbe f) +
            star
              (zetaCompletedAutocorrelationPrimePositiveFace ℓ.1 ℓ.2
                (zetaCompletedAutocorrelationProbe f))) := by
      exact congrArg
        (fun z : ℂ =>
          (zetaCompletedExplicitFormulaPrimeWeight ℓ.1 ℓ.2 : ℂ) *
            (z + star z))
        hface.symm

/-- Archimedean analytic convolution transform bridge before self-paired folding. -/
theorem zetaCompletedExplicitFormulaArchimedeanContribution_convolutionAutocorrelation_eq_weightedPaired
    (f : ZetaAdmissibleFunction) :
    zetaCompletedExplicitFormulaArchimedeanContribution
        (ZetaAdmissibleFunction.convolutionAutocorrelation f) =
      (2 : ℂ) *
        (zetaCompletedExplicitFormulaPhi f 0 *
          star (zetaCompletedExplicitFormulaPhi f 0)) := by
  unfold zetaCompletedExplicitFormulaArchimedeanContribution
  exact congrArg (fun z : ℂ => (2 : ℂ) * z)
    (by
      simpa using zetaCompletedExplicitFormulaPhi_convolutionAutocorrelation_real_pair f 0)

/-- The paired archimedean spectral packet contribution is the weighted paired product. -/
theorem zetaCompletedExplicitFormulaArchimedeanConvolutionPairedContribution_eq_weightedPaired
    (f : ZetaAdmissibleFunction) :
    zetaCompletedExplicitFormulaArchimedeanConvolutionPairedContribution f =
      (2 : ℂ) *
        (zetaCompletedExplicitFormulaPhi f 0 *
          star (zetaCompletedExplicitFormulaPhi f 0)) := by
  exact
    zetaCompletedExplicitFormulaArchimedeanConvolutionPairedContribution_eq_weightedPaired_owner f

theorem zetaCompletedExplicitFormulaArchimedeanContribution_convolutionAutocorrelation_eq_pairedSpectral
    (f : ZetaAdmissibleFunction) :
    zetaCompletedExplicitFormulaArchimedeanContribution
        (ZetaAdmissibleFunction.convolutionAutocorrelation f) =
      zetaCompletedExplicitFormulaArchimedeanConvolutionPairedContribution f := by
  exact
    (zetaCompletedExplicitFormulaArchimedeanContribution_convolutionAutocorrelation_eq_weightedPaired
      f).trans
      (zetaCompletedExplicitFormulaArchimedeanConvolutionPairedContribution_eq_weightedPaired
        f).symm

/-- Archimedean spectral convolution bridge after self-paired folding. -/
theorem zetaCompletedExplicitFormulaArchimedeanContribution_convolutionAutocorrelation_eq
    (f : ZetaAdmissibleFunction) :
    zetaCompletedExplicitFormulaArchimedeanContribution
        (ZetaAdmissibleFunction.convolutionAutocorrelation f) =
      zetaCompletedExplicitFormulaArchimedeanConvolutionContribution f := by
  exact
    zetaCompletedExplicitFormulaArchimedeanContribution_convolutionAutocorrelation_eq_pairedSpectral f

/-- The usual correction contribution of the admissible convolution autocorrelation probe is the
convolution-channel correction contribution. -/
theorem zetaCompletedExplicitFormulaCorrectionContribution_convolutionAutocorrelation_eq
    (f : ZetaAdmissibleFunction) :
    zetaCompletedExplicitFormulaCorrectionContribution
        (ZetaAdmissibleFunction.convolutionAutocorrelation f) =
      zetaCompletedExplicitFormulaCorrectionConvolutionContribution f := by
  exact Boundary.LFunctions.zetaCompletionCorrection_zero.symm

/-- The usual analytic boundary sum of the admissible convolution autocorrelation probe is the
completed time-side boundary channel. -/
theorem zetaCompletedExplicitFormulaBoundarySumAnalytic_convolutionAutocorrelation_eq_completedBoundaryChannel
    (f : ZetaAdmissibleFunction) :
    zetaCompletedExplicitFormulaBoundarySumAnalytic
        (ZetaAdmissibleFunction.convolutionAutocorrelation f) =
      completedBoundaryChannel (ZetaAdmissibleFunction.convolutionAutocorrelation f) := by
  unfold completedBoundaryChannel
  exact zetaCompletedExplicitFormulaBoundarySumAnalytic_eq_core
    (ZetaAdmissibleFunction.convolutionAutocorrelation f)

/-- The prime contribution is real on convolution-autocorrelation probes when the two-face/GNS
matrix coefficient is real-valued. -/
theorem zetaCompletedExplicitFormulaPrimeContribution_autocorrelation_im_eq_zero_of_twoFace_real
    (f : ZetaAdmissibleFunction)
    (hreal : Complex.im (zetaPrimeTwoFaceGNSMatrixCoefficient f) = 0) :
    Complex.im
        (zetaCompletedExplicitFormulaPrimeContribution
          (ZetaAdmissibleFunction.convolutionAutocorrelation f)) = 0 := by
  unfold zetaCompletedExplicitFormulaPrimeContribution
  unfold zetaCompletedExplicitFormulaPrimePowerContribution
  exact Complex.ofReal_im
    (∑' ι : ZetaPrimePowerIndex,
      -(ι.weight *
        Complex.re
          (zetaCompletedTimeBoundaryValue
              (ZetaAdmissibleFunction.convolutionAutocorrelation f) ι.center +
            star
              (zetaCompletedTimeBoundaryValue
                (ZetaAdmissibleFunction.convolutionAutocorrelation f) ι.center))))

/-- The prime contribution is real on convolution-autocorrelation probes because the owner
prime channel is the time-side real distribution coerced to `ℂ`. -/
theorem zetaCompletedExplicitFormulaPrimeContribution_autocorrelation_im_eq_zero
    (f : ZetaAdmissibleFunction) :
    Complex.im
        (zetaCompletedExplicitFormulaPrimeContribution
          (ZetaAdmissibleFunction.convolutionAutocorrelation f)) = 0 := by
  unfold zetaCompletedExplicitFormulaPrimeContribution
  unfold zetaCompletedExplicitFormulaPrimePowerContribution
  exact Complex.ofReal_im
    (∑' ι : ZetaPrimePowerIndex,
      -(ι.weight *
        Complex.re
          (zetaCompletedTimeBoundaryValue
              (ZetaAdmissibleFunction.convolutionAutocorrelation f) ι.center +
            star
              (zetaCompletedTimeBoundaryValue
                (ZetaAdmissibleFunction.convolutionAutocorrelation f) ι.center))))

/-- The archimedean contribution is real on convolution-autocorrelation probes under the
self-dual specialization. -/
theorem zetaCompletedExplicitFormulaArchimedeanContribution_autocorrelation_im_eq_zero_of_selfDual
    (f : ZetaAdmissibleFunction)
    (hself : zetaCompletedExplicitFormulaArchimedeanConvolutionContributionSelfDual f) :
    Complex.im
        (zetaCompletedExplicitFormulaArchimedeanContribution
          (ZetaAdmissibleFunction.convolutionAutocorrelation f)) = 0 := by
  have h :
      zetaCompletedExplicitFormulaArchimedeanContribution
          (ZetaAdmissibleFunction.convolutionAutocorrelation f) =
        zetaCompletedExplicitFormulaArchimedeanConvolutionContribution f :=
    zetaCompletedExplicitFormulaArchimedeanContribution_convolutionAutocorrelation_eq f
  exact (congrArg Complex.im h).trans
    (zetaCompletedExplicitFormulaArchimedeanConvolutionContribution_im_eq_zero_of_selfDual f hself)

/-- The archimedean contribution is real on convolution-autocorrelation probes by completed
boundary reconstruction, not by a self-duality condition on the seed. -/
theorem zetaCompletedExplicitFormulaArchimedeanContribution_autocorrelation_im_eq_zero
    (f : ZetaAdmissibleFunction) :
    Complex.im
        (zetaCompletedExplicitFormulaArchimedeanContribution
          (ZetaAdmissibleFunction.convolutionAutocorrelation f)) = 0 := by
  have h :
      zetaCompletedExplicitFormulaArchimedeanContribution
          (ZetaAdmissibleFunction.convolutionAutocorrelation f) =
        zetaCompletedExplicitFormulaArchimedeanConvolutionContribution f :=
    zetaCompletedExplicitFormulaArchimedeanContribution_convolutionAutocorrelation_eq f
  exact (congrArg Complex.im h).trans
    (zetaCompletedExplicitFormulaArchimedeanConvolutionContribution_im_eq_zero f)

/-- The correction contribution is real on convolution-autocorrelation probes. -/
theorem zetaCompletedExplicitFormulaCorrectionContribution_autocorrelation_im_eq_zero
    (f : ZetaAdmissibleFunction) :
    Complex.im
        (zetaCompletedExplicitFormulaCorrectionContribution
          (ZetaAdmissibleFunction.convolutionAutocorrelation f)) = 0 := by
  have hcorrection :
      zetaCompletedExplicitFormulaCorrectionContribution
          (ZetaAdmissibleFunction.convolutionAutocorrelation f) =
        zetaCompletionCorrection 0 :=
    Boundary.LFunctions.zetaCompletionCorrection_zero.symm
  exact (congrArg Complex.im hcorrection).trans
    Boundary.LFunctions.zetaCompletionCorrection_zero_im

/-- If the three explicit-formula boundary channels are real, then their analytic-core sum is
real. -/
theorem zetaCompletedExplicitFormulaBoundarySumCore_autocorrelation_im_eq_zero_of_components
    (f : ZetaAdmissibleFunction)
    (hprime :
      Complex.im
          (zetaCompletedExplicitFormulaPrimeContribution
            (ZetaAdmissibleFunction.convolutionAutocorrelation f)) = 0)
    (harch :
      Complex.im
          (zetaCompletedExplicitFormulaArchimedeanContribution
            (ZetaAdmissibleFunction.convolutionAutocorrelation f)) = 0)
    (hcorrection :
      Complex.im
          (zetaCompletedExplicitFormulaCorrectionContribution
            (ZetaAdmissibleFunction.convolutionAutocorrelation f)) = 0) :
    Complex.im
        (zetaCompletedExplicitFormulaBoundarySumCore
          (ZetaAdmissibleFunction.convolutionAutocorrelation f)) = 0 := by
  let g : ZetaAdmissibleFunction := ZetaAdmissibleFunction.convolutionAutocorrelation f
  let p : ℂ := zetaCompletedExplicitFormulaPrimeContribution g
  let a : ℂ := zetaCompletedExplicitFormulaArchimedeanContribution g
  let c : ℂ := zetaCompletedExplicitFormulaCorrectionContribution g
  have hcore :
      Complex.im (zetaCompletedExplicitFormulaBoundarySumCore g) =
        Complex.im (p + a + c) :=
    congrArg Complex.im (zetaCompletedExplicitFormulaBoundarySumCore_eq g)
  have hp : Complex.im p = 0 := hprime
  have ha : Complex.im a = 0 := harch
  have hc : Complex.im c = 0 := hcorrection
  calc
    Complex.im (zetaCompletedExplicitFormulaBoundarySumCore g) =
        Complex.im (p + a + c) := hcore
    _ = Complex.im (p + a) + Complex.im c := Complex.add_im (p + a) c
    _ = (Complex.im p + Complex.im a) + Complex.im c := by
      exact congrArg (fun x : ℝ => x + Complex.im c) (Complex.add_im p a)
    _ = (0 + 0) + 0 := by
      exact congrArg₂ (fun x y : ℝ => x + y)
        (congrArg₂ (fun x y : ℝ => x + y) hp ha)
        hc
    _ = 0 + 0 := by
      exact add_zero (0 + 0)
    _ = 0 := by
      exact zero_add 0

/-- The analytic-core boundary expression attached to a convolution-autocorrelation probe has
vanishing imaginary part. -/
theorem zetaCompletedExplicitFormulaBoundarySumCore_autocorrelation_im_eq_zero
    (f : ZetaAdmissibleFunction) :
    Complex.im
        (zetaCompletedExplicitFormulaBoundarySumCore
          (ZetaAdmissibleFunction.convolutionAutocorrelation f)) = 0 := by
  exact
    zetaCompletedExplicitFormulaBoundarySumCore_autocorrelation_im_eq_zero_of_components
      f
      (zetaCompletedExplicitFormulaPrimeContribution_autocorrelation_im_eq_zero f)
      (zetaCompletedExplicitFormulaArchimedeanContribution_autocorrelation_im_eq_zero f)
      (zetaCompletedExplicitFormulaCorrectionContribution_autocorrelation_im_eq_zero f)

/-- The analytic boundary sum of the admissible convolution autocorrelation probe agrees with
the completed time-side Krein scalar. -/
theorem zetaCompletedExplicitFormulaBoundarySumAnalytic_convolutionAutocorrelation_eq_seedKreinSum
    (f : ZetaAdmissibleFunction) :
    zetaCompletedExplicitFormulaBoundarySumAnalytic
        (ZetaAdmissibleFunction.convolutionAutocorrelation f) =
      (zetaCompletedExplicitFormulaAutocorrelationBoundaryKreinSum f : ℂ) := by
  let g : ZetaAdmissibleFunction := ZetaAdmissibleFunction.convolutionAutocorrelation f
  apply Complex.ext
  · unfold zetaCompletedExplicitFormulaAutocorrelationBoundaryKreinSum
    unfold zetaCompletedExplicitFormulaConvolutionAutocorrelationBoundaryKreinSum
    have hboundary :
        zetaCompletedExplicitFormulaBoundarySumAnalytic g =
          completedBoundaryChannel g := by
      unfold g
      exact
        zetaCompletedExplicitFormulaBoundarySumAnalytic_convolutionAutocorrelation_eq_completedBoundaryChannel
          f
    calc
      Complex.re (zetaCompletedExplicitFormulaBoundarySumAnalytic g) =
          Complex.re (completedBoundaryChannel g) := by
        exact congrArg Complex.re hboundary
      _ =
          Complex.re ((Complex.re (completedBoundaryChannel g)) : ℂ) := by
        exact (Complex.ofReal_re (Complex.re (completedBoundaryChannel g))).symm
  · unfold zetaCompletedExplicitFormulaAutocorrelationBoundaryKreinSum
    unfold zetaCompletedExplicitFormulaConvolutionAutocorrelationBoundaryKreinSum
    have hanalytic :
        zetaCompletedExplicitFormulaBoundarySumAnalytic g =
          zetaCompletedExplicitFormulaBoundarySumCore g :=
      zetaCompletedExplicitFormulaBoundarySumAnalytic_eq_core g
    calc
      Complex.im (zetaCompletedExplicitFormulaBoundarySumAnalytic g) =
          Complex.im (zetaCompletedExplicitFormulaBoundarySumCore g) := by
        exact congrArg Complex.im hanalytic
      _ = 0 := by
        unfold g
        exact zetaCompletedExplicitFormulaBoundarySumCore_autocorrelation_im_eq_zero f
      _ =
          Complex.im ((Complex.re (completedBoundaryChannel g)) : ℂ) := by
        exact (Complex.ofReal_im (Complex.re (completedBoundaryChannel g))).symm

/-- Legacy wrapper name for the corrected convolution-boundary normalization. -/
theorem zetaCompletedExplicitFormulaBoundarySumCore_autocorrelation_eq_seedKreinSum
    (f : ZetaAdmissibleFunction) :
    zetaCompletedExplicitFormulaBoundarySumAnalytic
        (ZetaAdmissibleFunction.convolutionAutocorrelation f) =
      (zetaCompletedExplicitFormulaAutocorrelationBoundaryKreinSum f : ℂ) := by
  exact zetaCompletedExplicitFormulaBoundarySumAnalytic_convolutionAutocorrelation_eq_seedKreinSum f

/-- Legacy wrapper name for the corrected convolution-boundary analytic normalization. -/
theorem zetaCompletedExplicitFormulaBoundarySumAnalytic_autocorrelation_eq_seedKreinSum
    (f : ZetaAdmissibleFunction) :
    zetaCompletedExplicitFormulaBoundarySumAnalytic
        (ZetaAdmissibleFunction.convolutionAutocorrelation f) =
      (zetaCompletedExplicitFormulaAutocorrelationBoundaryKreinSum f : ℂ) := by
  exact zetaCompletedExplicitFormulaBoundarySumAnalytic_convolutionAutocorrelation_eq_seedKreinSum f

/-- The analytic equality still required to complete the explicit formula. -/
def zetaCompletedExplicitFormulaAutocorrelationTarget
    (f : ZetaAdmissibleFunction) : Prop :=
  zetaCompletedZeroKreinGram f =
    zetaCompletedExplicitFormulaBoundarySum f

/-- The target proposition unfolds to the zero-side/boundary equality. -/
theorem zetaCompletedExplicitFormulaAutocorrelationTarget_iff
    (f : ZetaAdmissibleFunction) :
    zetaCompletedExplicitFormulaAutocorrelationTarget f ↔
      zetaCompletedZeroKreinGram f =
        zetaCompletedExplicitFormulaBoundarySum f := by
  rfl

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
