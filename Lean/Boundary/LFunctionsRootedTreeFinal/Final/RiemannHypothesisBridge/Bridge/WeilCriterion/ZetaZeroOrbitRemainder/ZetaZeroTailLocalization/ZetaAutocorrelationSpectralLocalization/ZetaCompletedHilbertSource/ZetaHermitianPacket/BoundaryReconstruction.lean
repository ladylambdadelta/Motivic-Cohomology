import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaCompletedHilbertSource.ZetaHermitianPacket.ConvolutionChannels

namespace Boundary
namespace LFunctions

noncomputable section

open Filter
open scoped Topology

namespace ZetaAdmissibleFunction

/-- The prime projection of the completed paired spectral packet is the prime convolution
paired contribution. -/
theorem zetaCompletedPairedSpectralBoundaryForm_prime_eq_contribution
    (f : ZetaAdmissibleFunction) :
    ZetaPairedSpectralPacketEnsemble.primePairedForm
        (zetaCompletedPairedSpectralBoundaryDefect f) =
      zetaCompletedExplicitFormulaPrimeConvolutionContribution f := by
  rfl

/-- The archimedean projection of the completed paired spectral packet is the archimedean
convolution paired contribution. -/
theorem zetaCompletedPairedSpectralBoundaryForm_archimedean_eq_contribution
    (f : ZetaAdmissibleFunction) :
    ZetaPairedSpectralPacketEnsemble.archimedeanPairedForm
        (zetaCompletedPairedSpectralBoundaryDefect f) =
      zetaCompletedExplicitFormulaArchimedeanConvolutionContribution f := by
  rfl

/-- The correction projection of the completed paired spectral packet is the correction
convolution paired contribution. -/
theorem zetaCompletedPairedSpectralBoundaryForm_correction_eq_contribution
    (f : ZetaAdmissibleFunction) :
    ZetaPairedSpectralPacketEnsemble.correctionPairedForm
        (zetaCompletedPairedSpectralBoundaryDefect f) =
      zetaCompletedExplicitFormulaCorrectionConvolutionContribution f := by
  rfl

/-- The completed paired spectral boundary form is the sum of the three convolution-channel
contributions. -/
theorem zetaCompletedPairedSpectralBoundaryForm_eq_convolutionContributions
    (f : ZetaAdmissibleFunction) :
    zetaCompletedPairedSpectralBoundaryForm f =
      zetaCompletedExplicitFormulaPrimeConvolutionContribution f +
        zetaCompletedExplicitFormulaArchimedeanConvolutionContribution f +
        zetaCompletedExplicitFormulaCorrectionConvolutionContribution f := by
  have hsplit :
      ZetaPairedSpectralPacketEnsemble.pairedForm
          (zetaCompletedPairedSpectralBoundaryDefect f) =
        ZetaPairedSpectralPacketEnsemble.primePairedForm
            (zetaCompletedPairedSpectralBoundaryDefect f) +
          ZetaPairedSpectralPacketEnsemble.archimedeanPairedForm
            (zetaCompletedPairedSpectralBoundaryDefect f) +
          ZetaPairedSpectralPacketEnsemble.correctionPairedForm
            (zetaCompletedPairedSpectralBoundaryDefect f) :=
    ZetaPairedSpectralPacketEnsemble.pairedForm_eq_prime_add_archimedean_add_correction
      (zetaCompletedPairedSpectralBoundaryDefect f)
  have hprime :
      ZetaPairedSpectralPacketEnsemble.primePairedForm
          (zetaCompletedPairedSpectralBoundaryDefect f) =
        zetaCompletedExplicitFormulaPrimeConvolutionContribution f :=
    zetaCompletedPairedSpectralBoundaryForm_prime_eq_contribution f
  have harch :
      ZetaPairedSpectralPacketEnsemble.archimedeanPairedForm
          (zetaCompletedPairedSpectralBoundaryDefect f) =
        zetaCompletedExplicitFormulaArchimedeanConvolutionContribution f :=
    zetaCompletedPairedSpectralBoundaryForm_archimedean_eq_contribution f
  have hcorrection :
      ZetaPairedSpectralPacketEnsemble.correctionPairedForm
          (zetaCompletedPairedSpectralBoundaryDefect f) =
        zetaCompletedExplicitFormulaCorrectionConvolutionContribution f :=
    zetaCompletedPairedSpectralBoundaryForm_correction_eq_contribution f
  exact hsplit.trans
    (congrArg₂ (fun x y : ℂ => x + y)
      (congrArg₂ (fun x y : ℂ => x + y) hprime harch)
      hcorrection)

/-- Completed boundary reconstruction into the realized Gram channel. This is the direct
explicit-formula reconstruction statement; it does not identify the realized Gram with an
amplitude norm-square packet. -/
theorem zetaCompletedBoundaryReconstruction_pairedForm_eq_realizedGram
    (f : ZetaAdmissibleFunction) :
    zetaCompletedPairedSpectralBoundaryForm f =
      zetaCompletedBoundaryRealizedGram f := by
  have hpaired :
      zetaCompletedPairedSpectralBoundaryForm f =
        zetaCompletedExplicitFormulaPrimeConvolutionContribution f +
          zetaCompletedExplicitFormulaArchimedeanConvolutionContribution f +
          zetaCompletedExplicitFormulaCorrectionConvolutionContribution f :=
    zetaCompletedPairedSpectralBoundaryForm_eq_convolutionContributions f
  have hprime :
      zetaCompletedExplicitFormulaPrimeConvolutionContribution f =
        zetaCompletedPrimeBoundaryRealizedGram f := by
    exact (zetaCompletedExplicitFormulaPrimeConvolutionContribution_eq_paired f).trans
      (zetaCompletedPrimeBoundaryReconstruction_pairing_eq_realizedGram f)
  have harch :
      zetaCompletedExplicitFormulaArchimedeanConvolutionContribution f =
        zetaCompletedArchimedeanBoundaryRealizedGram f := by
    exact (zetaCompletedExplicitFormulaArchimedeanConvolutionContribution_eq_paired f).trans
      (zetaCompletedArchimedeanBoundaryReconstruction_pairing_eq_realizedGram f)
  have hcorrection :
      zetaCompletedExplicitFormulaCorrectionConvolutionContribution f =
        zetaCompletedCorrectionBoundaryRealizedGram f :=
    zetaCompletedCorrectionBoundaryReconstruction_pairing_eq_realizedGram f
  have hcomponents :
      zetaCompletedExplicitFormulaPrimeConvolutionContribution f +
          zetaCompletedExplicitFormulaArchimedeanConvolutionContribution f +
          zetaCompletedExplicitFormulaCorrectionConvolutionContribution f =
        zetaCompletedPrimeBoundaryRealizedGram f +
          zetaCompletedArchimedeanBoundaryRealizedGram f +
          zetaCompletedCorrectionBoundaryRealizedGram f :=
    congrArg₂ (fun x y : ℂ => x + y)
      (congrArg₂ (fun x y : ℂ => x + y) hprime harch)
      hcorrection
  have hrealized :
      zetaCompletedPrimeBoundaryRealizedGram f +
          zetaCompletedArchimedeanBoundaryRealizedGram f +
          zetaCompletedCorrectionBoundaryRealizedGram f =
        zetaCompletedBoundaryRealizedGram f := by
    rfl
  exact hpaired.trans (hcomponents.trans hrealized)

/-- The finite realized boundary form is represented by the finite mixed symmetrized boundary
package: the prime channel is the finite two-face/GNS matrix coefficient, while the
archimedean and correction channels are one-face Hermitian squares. -/
theorem zetaCompletedBoundaryRealizedGram_eq_finiteGNSSymmetrizedBoundaryForm
    (f : ZetaAdmissibleFunction) :
    zetaCompletedBoundaryRealizedGram f =
      zetaFiniteGNSSymmetrizedBoundaryForm f := by
  have hprime :
      zetaCompletedPrimeBoundaryRealizedGram f =
        zetaPrimeTwoFaceGNSMatrixCoefficient f :=
    zetaCompletedPrimeBoundaryRealizedGram_eq_twoFacePrimeMatrixCoefficient f
  have harch :
      zetaCompletedArchimedeanBoundaryRealizedGram f =
        (ZetaHermitianPacketEnsemble.archimedeanPacketGram
          (zetaCompletedHermitianBoundaryDefect f) : ℂ) :=
    zetaCompletedArchimedeanBoundaryRealizedGram_eq_hermitianArchimedeanPacketGram f
  have hcorrection :
      zetaCompletedCorrectionBoundaryRealizedGram f =
        (ZetaHermitianPacketEnsemble.correctionPacketGram
          (zetaCompletedHermitianBoundaryDefect f) : ℂ) := by
    exact (zetaCompletedCorrectionBoundaryReconstruction_pairing_eq_realizedGram f).symm.trans
      (zetaCompletedCorrectionBoundaryReconstruction_pairing_eq_gram f)
  have hcomponents :
      zetaCompletedPrimeBoundaryRealizedGram f +
          zetaCompletedArchimedeanBoundaryRealizedGram f +
          zetaCompletedCorrectionBoundaryRealizedGram f =
        zetaPrimeTwoFaceGNSMatrixCoefficient f +
          (ZetaHermitianPacketEnsemble.archimedeanPacketGram
            (zetaCompletedHermitianBoundaryDefect f) : ℂ) +
          (ZetaHermitianPacketEnsemble.correctionPacketGram
            (zetaCompletedHermitianBoundaryDefect f) : ℂ) :=
    congrArg₂ (fun x y : ℂ => x + y)
      (congrArg₂ (fun x y : ℂ => x + y) hprime harch)
      hcorrection
  calc
    zetaCompletedBoundaryRealizedGram f =
        zetaCompletedPrimeBoundaryRealizedGram f +
          zetaCompletedArchimedeanBoundaryRealizedGram f +
          zetaCompletedCorrectionBoundaryRealizedGram f := by
      rfl
    _ =
        zetaPrimeTwoFaceGNSMatrixCoefficient f +
          (ZetaHermitianPacketEnsemble.archimedeanPacketGram
            (zetaCompletedHermitianBoundaryDefect f) : ℂ) +
          (ZetaHermitianPacketEnsemble.correctionPacketGram
            (zetaCompletedHermitianBoundaryDefect f) : ℂ) := hcomponents
    _ = zetaFiniteGNSSymmetrizedBoundaryForm f := by
      rfl

/-- Finite boundary reconstruction into the finite symmetrized real two-face presentation. -/
theorem zetaCompletedBoundaryReconstruction_pairedForm_eq_finiteGNSSymmetrizedBoundaryForm
    (f : ZetaAdmissibleFunction) :
    zetaCompletedPairedSpectralBoundaryForm f =
      zetaFiniteGNSSymmetrizedBoundaryForm f := by
  exact (zetaCompletedBoundaryReconstruction_pairedForm_eq_realizedGram f).trans
    (zetaCompletedBoundaryRealizedGram_eq_finiteGNSSymmetrizedBoundaryForm f)

/-- The completed mixed GNS boundary form is real-valued: the real prime channel is the
symmetrized two-face coefficient, and the remaining packet Gram coordinates are real
coercions. -/
theorem zetaCompletedGNSSymmetrizedBoundaryForm_im_eq_zero
    (f : ZetaAdmissibleFunction) :
    Complex.im (zetaCompletedGNSSymmetrizedBoundaryForm f) = 0 := by
  let z : ℂ := zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f
  let a : ℂ :=
    (ZetaHermitianPacketEnsemble.archimedeanPacketGram
      (zetaCompletedHermitianBoundaryDefect f) : ℂ)
  let c : ℂ :=
    (ZetaHermitianPacketEnsemble.correctionPacketGram
      (zetaCompletedHermitianBoundaryDefect f) : ℂ)
  have hz : Complex.im z = 0 := by
    exact zetaCompletedPrimeTwoFaceGNSMatrixCoefficient_im_eq_zero f
  have ha : Complex.im a = 0 := by
    exact Complex.ofReal_im
      (ZetaHermitianPacketEnsemble.archimedeanPacketGram
        (zetaCompletedHermitianBoundaryDefect f))
  have hc : Complex.im c = 0 := by
    exact Complex.ofReal_im
      (ZetaHermitianPacketEnsemble.correctionPacketGram
        (zetaCompletedHermitianBoundaryDefect f))
  have hza : Complex.im z + Complex.im a = 0 := by
    calc
      Complex.im z + Complex.im a = 0 + Complex.im a := by
        exact congrArg (fun x : ℝ => x + Complex.im a) hz
      _ = 0 + 0 := by
        exact congrArg (fun x : ℝ => 0 + x) ha
      _ = 0 := by
        exact add_zero 0
  calc
    Complex.im (z + a + c) = Complex.im (z + a) + Complex.im c := by
      exact Complex.add_im (z + a) c
    _ = (Complex.im z + Complex.im a) + Complex.im c := by
      exact congrArg (fun x : ℝ => x + Complex.im c) (Complex.add_im z a)
    _ = 0 + Complex.im c := by
      exact congrArg (fun x : ℝ => x + Complex.im c) hza
    _ = 0 + 0 := by
      exact congrArg (fun x : ℝ => 0 + x) hc
    _ = 0 := by
      exact add_zero 0

/-- The compatibility GNS boundary presentation is real-valued because it is the symmetrized
two-face presentation. -/
theorem zetaCompletedGNSBoundaryForm_im_eq_zero
    (f : ZetaAdmissibleFunction) :
    Complex.im (zetaCompletedGNSBoundaryForm f) = 0 := by
  exact zetaCompletedGNSSymmetrizedBoundaryForm_im_eq_zero f

/-- The symmetrized completed GNS boundary form is definitionally the compatibility GNS
boundary presentation in this spectral packet layer.  Positivity is owned downstream by the
completed defect-kernel channel, where diagonal debt and debt absorption are visible. -/
theorem zetaCompletedGNSSymmetrizedBoundaryForm_eq_GNSBoundaryForm
    (f : ZetaAdmissibleFunction) :
    zetaCompletedGNSSymmetrizedBoundaryForm f =
      zetaCompletedGNSBoundaryForm f := by
  rfl

/-- The finite display-level symmetrized boundary form is real-valued. -/
theorem zetaFiniteGNSSymmetrizedBoundaryForm_im_eq_zero
    (f : ZetaAdmissibleFunction) :
    Complex.im (zetaFiniteGNSSymmetrizedBoundaryForm f) = 0 := by
  let z : ℂ := zetaPrimeTwoFaceGNSMatrixCoefficient f
  let a : ℂ :=
    (ZetaHermitianPacketEnsemble.archimedeanPacketGram
      (zetaCompletedHermitianBoundaryDefect f) : ℂ)
  let c : ℂ :=
    (ZetaHermitianPacketEnsemble.correctionPacketGram
      (zetaCompletedHermitianBoundaryDefect f) : ℂ)
  have hz : Complex.im z = 0 := by
    exact zetaPrimeTwoFaceGNSMatrixCoefficient_im_eq_zero f
  have ha : Complex.im a = 0 := by
    exact Complex.ofReal_im
      (ZetaHermitianPacketEnsemble.archimedeanPacketGram
        (zetaCompletedHermitianBoundaryDefect f))
  have hc : Complex.im c = 0 := by
    exact Complex.ofReal_im
      (ZetaHermitianPacketEnsemble.correctionPacketGram
        (zetaCompletedHermitianBoundaryDefect f))
  have hza : Complex.im z + Complex.im a = 0 := by
    calc
      Complex.im z + Complex.im a = 0 + Complex.im a := by
        exact congrArg (fun x : ℝ => x + Complex.im a) hz
      _ = 0 + 0 := by
        exact congrArg (fun x : ℝ => 0 + x) ha
      _ = 0 := by
        exact add_zero 0
  calc
    Complex.im (z + a + c) = Complex.im (z + a) + Complex.im c := by
      exact Complex.add_im (z + a) c
    _ = (Complex.im z + Complex.im a) + Complex.im c := by
      exact congrArg (fun x : ℝ => x + Complex.im c) (Complex.add_im z a)
    _ = 0 + Complex.im c := by
      exact congrArg (fun x : ℝ => x + Complex.im c) hza
    _ = 0 + 0 := by
      exact congrArg (fun x : ℝ => 0 + x) hc
    _ = 0 := by
      exact add_zero 0

/-- The completed paired spectral boundary form is real-valued. -/
theorem zetaCompletedPairedSpectralBoundaryForm_im_eq_zero
    (f : ZetaAdmissibleFunction) :
    Complex.im (zetaCompletedPairedSpectralBoundaryForm f) = 0 := by
  have hform :
      zetaCompletedPairedSpectralBoundaryForm f =
        zetaFiniteGNSSymmetrizedBoundaryForm f :=
    zetaCompletedBoundaryReconstruction_pairedForm_eq_finiteGNSSymmetrizedBoundaryForm f
  exact (congrArg Complex.im hform).trans
    (zetaFiniteGNSSymmetrizedBoundaryForm_im_eq_zero f)

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
