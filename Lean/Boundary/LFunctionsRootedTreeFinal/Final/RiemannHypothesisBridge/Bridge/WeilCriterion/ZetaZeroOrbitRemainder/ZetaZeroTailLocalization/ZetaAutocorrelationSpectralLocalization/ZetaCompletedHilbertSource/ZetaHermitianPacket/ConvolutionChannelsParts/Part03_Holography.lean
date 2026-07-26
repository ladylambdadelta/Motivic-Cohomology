import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaCompletedHilbertSource.ZetaHermitianPacket.ConvolutionChannelsParts.Part02_Reconstruction

namespace Boundary
namespace LFunctions

noncomputable section

open Filter
open scoped Topology

namespace ZetaAdmissibleFunction

/-- The real part of the prime convolution contribution is the real part of the reconstructed
two-face/GNS matrix coefficient. -/
theorem zetaCompletedExplicitFormulaPrimeConvolutionContribution_re_eq_twoFaceMatrixCoefficient
    (f : ZetaAdmissibleFunction) :
    Complex.re (zetaCompletedExplicitFormulaPrimeConvolutionContribution f) =
      Complex.re (zetaPrimeTwoFaceGNSMatrixCoefficient f) := by
  exact congrArg Complex.re
    (zetaCompletedExplicitFormulaPrimeConvolutionContribution_eq_twoFaceMatrixCoefficient f)

/-- The prime convolution contribution is real-valued when the two-face/GNS matrix coefficient
is real-valued. -/
theorem zetaCompletedExplicitFormulaPrimeConvolutionContribution_im_eq_zero_of_twoFace_real
    (f : ZetaAdmissibleFunction)
    (hreal : Complex.im (zetaPrimeTwoFaceGNSMatrixCoefficient f) = 0) :
    Complex.im (zetaCompletedExplicitFormulaPrimeConvolutionContribution f) = 0 := by
  exact (congrArg Complex.im
    (zetaCompletedExplicitFormulaPrimeConvolutionContribution_eq_twoFaceMatrixCoefficient f)).trans
    hreal

/-- The reconstructed prime convolution contribution is real-valued. -/
theorem zetaCompletedExplicitFormulaPrimeConvolutionContribution_im_eq_zero
    (f : ZetaAdmissibleFunction) :
    Complex.im (zetaCompletedExplicitFormulaPrimeConvolutionContribution f) = 0 := by
  exact zetaCompletedExplicitFormulaPrimeConvolutionContribution_im_eq_zero_of_twoFace_real
    f (zetaPrimeTwoFaceGNSMatrixCoefficient_im_eq_zero f)

/-- The reconstructed archimedean convolution contribution is real-valued. -/
theorem zetaCompletedExplicitFormulaArchimedeanConvolutionContribution_im_eq_zero
    (f : ZetaAdmissibleFunction) :
    Complex.im (zetaCompletedExplicitFormulaArchimedeanConvolutionContribution f) = 0 := by
  exact (congrArg Complex.im
    (zetaCompletedExplicitFormulaArchimedeanConvolutionContribution_eq_archimedeanPacketGram f)).trans
    (Complex.ofReal_im
      (ZetaHermitianPacketEnsemble.archimedeanPacketGram
        (zetaCompletedHermitianBoundaryDefect f)))

/-- The real part of the reconstructed archimedean convolution contribution is the Hermitian
archimedean packet Gram. -/
theorem zetaCompletedExplicitFormulaArchimedeanConvolutionContribution_re_eq_archimedeanPacketGram
    (f : ZetaAdmissibleFunction) :
    Complex.re (zetaCompletedExplicitFormulaArchimedeanConvolutionContribution f) =
      ZetaHermitianPacketEnsemble.archimedeanPacketGram
        (zetaCompletedHermitianBoundaryDefect f) := by
  exact congrArg Complex.re
    (zetaCompletedExplicitFormulaArchimedeanConvolutionContribution_eq_archimedeanPacketGram f)

/-- The autocorrelation correction channel unfolds to the centered coefficient times the
self-paired transform value. -/
theorem zetaCompletedExplicitFormulaCorrectionConvolutionContribution_eq_four_phi_pair
    (f : ZetaAdmissibleFunction) :
    zetaCompletedExplicitFormulaCorrectionConvolutionContribution f =
      (4 : ℂ) *
        (zetaCompletedExplicitFormulaPhi f 0 *
          star (zetaCompletedExplicitFormulaPhi f 0)) := by
  have hcoeff :
      1 / (1 / 2 : ℂ) + 1 / (1 - (1 / 2 : ℂ)) = (4 : ℂ) :=
    zetaCompletionCorrection_zero.symm.trans zetaCompletionCorrection_zero_eq_four
  have hzero :
      zetaCompletedExplicitFormulaPhi
          (ZetaAdmissibleFunction.convolutionAutocorrelation f) 0 =
        zetaCompletedExplicitFormulaPhi f 0 *
          star (zetaCompletedExplicitFormulaPhi f 0) := by
    have hpair :=
      zetaCompletedExplicitFormulaPhi_convolutionAutocorrelation_real_pair f 0
    have hneg :
        zetaCompletedExplicitFormulaPhi f (-(0 : ℂ)) =
          zetaCompletedExplicitFormulaPhi f 0 := by
      exact congrArg (zetaCompletedExplicitFormulaPhi f) (neg_zero : -(0 : ℂ) = 0)
    exact hpair.trans
      (congrArg
        (fun z : ℂ => zetaCompletedExplicitFormulaPhi f 0 * star z)
        hneg)
  calc
    zetaCompletedExplicitFormulaCorrectionConvolutionContribution f =
        (1 / (1 / 2 : ℂ) + 1 / (1 - (1 / 2 : ℂ))) *
          zetaCompletedExplicitFormulaPhi
            (ZetaAdmissibleFunction.convolutionAutocorrelation f) 0 := by
      exact zetaCompletedExplicitFormulaCorrectionContribution_eq
        (ZetaAdmissibleFunction.convolutionAutocorrelation f)
    _ =
        (4 : ℂ) *
          zetaCompletedExplicitFormulaPhi
            (ZetaAdmissibleFunction.convolutionAutocorrelation f) 0 := by
      exact congrArg
        (fun c : ℂ =>
          c *
            zetaCompletedExplicitFormulaPhi
              (ZetaAdmissibleFunction.convolutionAutocorrelation f) 0)
        hcoeff
    _ =
        (4 : ℂ) *
          (zetaCompletedExplicitFormulaPhi f 0 *
            star (zetaCompletedExplicitFormulaPhi f 0)) := by
      exact congrArg (fun z : ℂ => (4 : ℂ) * z) hzero

/-- The correction Hermitian packet Gram is the square of the centered correction amplitude
`2 * Φ_f(0)`, hence the same `4 * Φ_f(0) * star Φ_f(0)` scalar. -/
theorem zetaCompletedHermitianBoundaryDefect_correctionPacketGram_eq_four_phi_pair
    (f : ZetaAdmissibleFunction) :
    (ZetaHermitianPacketEnsemble.correctionPacketGram
        (zetaCompletedHermitianBoundaryDefect f) : ℂ) =
      (4 : ℂ) *
        (zetaCompletedExplicitFormulaPhi f 0 *
          star (zetaCompletedExplicitFormulaPhi f 0)) := by
  let c : ℝ := zetaCompletionCorrectionPacketCoordinate
  let a : ℂ := zetaCompletedExplicitFormulaPhi f 0
  have hgram :
      ZetaHermitianPacketEnsemble.correctionPacketGram
          (zetaCompletedHermitianBoundaryDefect f) =
        ZetaHermitianPacketEnsemble.coordinateGram ((c : ℂ) * a) :=
    zetaCompletedHermitianBoundaryDefect_correctionPacketGram_eq_centeredPolePhiNormSq f
  have hc_sq_real : c * c = 4 := by
    exact zetaCompletionCorrectionPacketCoordinate_sq.trans
      zetaCompletionCorrection_zero_re
  have hc_sq_complex : (c : ℂ) * (c : ℂ) = (4 : ℂ) := by
    calc
      (c : ℂ) * (c : ℂ) = ((c * c : ℝ) : ℂ) := by
        exact (Complex.ofReal_mul c c).symm
      _ = (4 : ℂ) := by
        exact congrArg (fun x : ℝ => (x : ℂ)) hc_sq_real
  have hc_star : star (c : ℂ) = (c : ℂ) := by
    exact Complex.conj_ofReal c
  have hstar : star ((c : ℂ) * a) = (c : ℂ) * star a := by
    calc
      star ((c : ℂ) * a) = star a * star (c : ℂ) := by
        exact star_mul (c : ℂ) a
      _ = star a * (c : ℂ) := by
        exact congrArg (fun z : ℂ => star a * z) hc_star
      _ = (c : ℂ) * star a := by
        exact mul_comm (star a) (c : ℂ)
  have hcoord :
      (ZetaHermitianPacketEnsemble.coordinateGram ((c : ℂ) * a) : ℂ) =
        (4 : ℂ) * (a * star a) := by
    calc
      (ZetaHermitianPacketEnsemble.coordinateGram ((c : ℂ) * a) : ℂ) =
          ((c : ℂ) * a) * star ((c : ℂ) * a) := by
        exact (Complex.mul_conj ((c : ℂ) * a)).symm
      _ = ((c : ℂ) * a) * ((c : ℂ) * star a) := by
        exact congrArg (fun z : ℂ => ((c : ℂ) * a) * z) hstar
      _ = ((c : ℂ) * (c : ℂ)) * (a * star a) := by
        calc
          ((c : ℂ) * a) * ((c : ℂ) * star a) =
              (c : ℂ) * (a * ((c : ℂ) * star a)) := by
            exact mul_assoc (c : ℂ) a ((c : ℂ) * star a)
          _ = (c : ℂ) * ((a * (c : ℂ)) * star a) := by
            exact congrArg (fun z : ℂ => (c : ℂ) * z)
              ((mul_assoc a (c : ℂ) (star a)).symm)
          _ = (c : ℂ) * (((c : ℂ) * a) * star a) := by
            exact congrArg (fun z : ℂ => (c : ℂ) * (z * star a))
              (mul_comm a (c : ℂ))
          _ = (c : ℂ) * ((c : ℂ) * (a * star a)) := by
            exact congrArg (fun z : ℂ => (c : ℂ) * z)
              (mul_assoc (c : ℂ) a (star a))
          _ = ((c : ℂ) * (c : ℂ)) * (a * star a) := by
            exact (mul_assoc (c : ℂ) (c : ℂ) (a * star a)).symm
      _ = (4 : ℂ) * (a * star a) := by
        exact congrArg (fun z : ℂ => z * (a * star a)) hc_sq_complex
  calc
    (ZetaHermitianPacketEnsemble.correctionPacketGram
        (zetaCompletedHermitianBoundaryDefect f) : ℂ) =
        (ZetaHermitianPacketEnsemble.coordinateGram ((c : ℂ) * a) : ℂ) := by
      exact congrArg (fun r : ℝ => (r : ℂ)) hgram
    _ = (4 : ℂ) * (a * star a) := hcoord

/-- The centered-pole correction contribution on the autocorrelation probe is the Hermitian
correction packet Gram. This is the downstream correction-normalization owner theorem after
the correction contribution was changed from the old constant to the centered-pole
`Φ_f(0)` value. -/
theorem zetaCompletedExplicitFormulaCorrectionConvolutionContribution_eq_centeredPolePhiPacketGram
    (f : ZetaAdmissibleFunction) :
    zetaCompletedExplicitFormulaCorrectionConvolutionContribution f =
      (ZetaHermitianPacketEnsemble.correctionPacketGram
        (zetaCompletedHermitianBoundaryDefect f) : ℂ) := by
  exact (zetaCompletedExplicitFormulaCorrectionConvolutionContribution_eq_four_phi_pair f).trans
    (zetaCompletedHermitianBoundaryDefect_correctionPacketGram_eq_four_phi_pair f).symm

/-- The correction convolution contribution is real-valued. -/
theorem zetaCompletedExplicitFormulaCorrectionConvolutionContribution_im_eq_zero
    (f : ZetaAdmissibleFunction) :
    Complex.im (zetaCompletedExplicitFormulaCorrectionConvolutionContribution f) = 0 := by
  calc
    Complex.im (zetaCompletedExplicitFormulaCorrectionConvolutionContribution f) =
        Complex.im
          (ZetaHermitianPacketEnsemble.correctionPacketGram
            (zetaCompletedHermitianBoundaryDefect f) : ℂ) := by
      exact congrArg Complex.im
        (zetaCompletedExplicitFormulaCorrectionConvolutionContribution_eq_centeredPolePhiPacketGram
          f)
    _ = 0 := by
      exact Complex.ofReal_im
        (ZetaHermitianPacketEnsemble.correctionPacketGram
          (zetaCompletedHermitianBoundaryDefect f))

/-- Prime-channel two-face/GNS holography. -/
theorem zetaCompletedExplicitFormulaPrimeConvolutionChannel_holographic_twoFace
    (f : ZetaAdmissibleFunction) :
    Complex.re (zetaCompletedExplicitFormulaPrimeConvolutionContribution f) =
      Complex.re (zetaPrimeTwoFaceGNSMatrixCoefficient f) := by
  exact zetaCompletedExplicitFormulaPrimeConvolutionContribution_re_eq_twoFaceMatrixCoefficient f

/-- Archimedean-channel norm-square holography. -/
theorem zetaCompletedExplicitFormulaArchimedeanConvolutionChannel_holographic
    (f : ZetaAdmissibleFunction) :
    Complex.re (zetaCompletedExplicitFormulaArchimedeanConvolutionContribution f) =
      ZetaHermitianPacketEnsemble.archimedeanPacketGram
        (zetaCompletedHermitianBoundaryDefect f) := by
  exact zetaCompletedExplicitFormulaArchimedeanConvolutionContribution_re_eq_archimedeanPacketGram f

/-- Correction-channel holography for the normalized Hermitian correction packet. -/
theorem zetaCompletedExplicitFormulaCorrectionConvolutionChannel_holographic
    (f : ZetaAdmissibleFunction) :
    Complex.re (zetaCompletedExplicitFormulaCorrectionConvolutionContribution f) =
      ZetaHermitianPacketEnsemble.correctionPacketGram
        (zetaCompletedHermitianBoundaryDefect f) := by
  calc
    Complex.re (zetaCompletedExplicitFormulaCorrectionConvolutionContribution f) =
        Complex.re
          (ZetaHermitianPacketEnsemble.correctionPacketGram
            (zetaCompletedHermitianBoundaryDefect f) : ℂ) := by
      exact congrArg Complex.re
        (zetaCompletedExplicitFormulaCorrectionConvolutionContribution_eq_centeredPolePhiPacketGram
          f)
    _ =
        ZetaHermitianPacketEnsemble.correctionPacketGram
          (zetaCompletedHermitianBoundaryDefect f) := by
      exact Complex.ofReal_re
        (ZetaHermitianPacketEnsemble.correctionPacketGram
          (zetaCompletedHermitianBoundaryDefect f))

/-- Correction completed boundary reconstruction. -/
theorem zetaCompletedCorrectionBoundaryReconstruction_pairing_eq_gram
    (f : ZetaAdmissibleFunction) :
    zetaCompletedExplicitFormulaCorrectionConvolutionContribution f =
      (ZetaHermitianPacketEnsemble.correctionPacketGram
        (zetaCompletedHermitianBoundaryDefect f) : ℂ) := by
  exact
    zetaCompletedExplicitFormulaCorrectionConvolutionContribution_eq_centeredPolePhiPacketGram
      f
end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
