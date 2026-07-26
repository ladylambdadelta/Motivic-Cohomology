import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaCompletedHilbertSource.ZetaPacketComparison.ZetaCompletedBoundaryDefect.ZetaPacketReconstruction.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaCompletedHilbertSource.ZetaPacketComparison.ZetaCompletionCorrection.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaAdmissibleSpectralInterpolation.ZetaAdmissiblePaleyWiener.ZetaExplicitFormulaAnalyticCore.OwnerParts.BoundaryChannels

/-!
# Boundary completed zeta defect

This file owns the completed boundary-defect operator attached to an
admissible probe. It packages the prime, archimedean, and completion/correction
components into the single boundary object whose Gram norm is the packet
energy.

The comparison to the completed Weil form is deferred to the comparison file.
-/

namespace Boundary
namespace LFunctions

noncomputable section

namespace ZetaAdmissibleFunction

/-- Helper: The completion correction packet coordinate is nonzero. -/
private lemma zetaCompletionCorrectionPacketCoordinate_ne_zero :
    zetaCompletionCorrectionPacketCoordinate ≠ 0 := by
  unfold zetaCompletionCorrectionPacketCoordinate
  exact two_ne_zero

/-- The prime component of the completed zeta boundary defect. -/
noncomputable def zetaCompletedBoundaryDefectPrime (f : ZetaAdmissibleFunction) :
    ZetaPacketEnsemble :=
  canonicalZetaPrimePacketAsEnsemble f

/-- The archimedean component of the completed zeta boundary defect. -/
noncomputable def zetaCompletedBoundaryDefectArchimedean (f : ZetaAdmissibleFunction) :
    ZetaPacketEnsemble :=
  zetaArchimedeanPacketAsEnsemble f

/-- The completion/correction component of the completed zeta boundary defect. -/
noncomputable def zetaCompletedBoundaryDefectCorrection (f : ZetaAdmissibleFunction) :
    ZetaPacketEnsemble :=
  zetaCorrectionPacketAsEnsemble f

/-- The completed zeta boundary defect attached to an admissible probe. -/
noncomputable def zetaCompletedBoundaryDefect (f : ZetaAdmissibleFunction) :
    ZetaPacketEnsemble :=
  zetaCompletedBoundaryDefectPrime f +
    zetaCompletedBoundaryDefectArchimedean f +
    zetaCompletedBoundaryDefectCorrection f

/-- A prime packet has zero correction coordinate. -/
theorem zetaPrimePacketAsEnsemble_correction_apply_at_bound
    (f : ZetaAdmissibleFunction) (B : ℝ) :
    zetaPrimePacketAsEnsemble f B ZetaPacketLabel.correction = 0 := by
  unfold zetaPrimePacketAsEnsemble ZetaPacketEnsemble.single
  calc
    (∑ ℓ in zetaPacketPrimeSupport B,
        (Finsupp.single (ZetaPacketLabel.prime ℓ.1 ℓ.2)
          (Complex.re
            (zetaPrimePacketWeight (ZetaPacketLabel.prime ℓ.1 ℓ.2) •
              ZetaTestFunction.primePacketTranslationDefect ℓ.1 ℓ.2
                f.toZetaTestFunction' 0)) : ZetaPacketEnsemble))
        ZetaPacketLabel.correction =
        ∑ ℓ in zetaPacketPrimeSupport B,
          (Finsupp.single (ZetaPacketLabel.prime ℓ.1 ℓ.2)
            (Complex.re
              (zetaPrimePacketWeight (ZetaPacketLabel.prime ℓ.1 ℓ.2) •
                ZetaTestFunction.primePacketTranslationDefect ℓ.1 ℓ.2
                  f.toZetaTestFunction' 0)) : ZetaPacketEnsemble)
            ZetaPacketLabel.correction := by
      exact Finsupp.finset_sum_apply (zetaPacketPrimeSupport B)
        (fun ℓ =>
          (Finsupp.single (ZetaPacketLabel.prime ℓ.1 ℓ.2)
            (Complex.re
              (zetaPrimePacketWeight (ZetaPacketLabel.prime ℓ.1 ℓ.2) •
                ZetaTestFunction.primePacketTranslationDefect ℓ.1 ℓ.2
                  f.toZetaTestFunction' 0)) : ZetaPacketEnsemble))
        ZetaPacketLabel.correction
    _ = 0 := by
      exact Finset.sum_eq_zero
        (fun ℓ _ =>
          Finsupp.single_eq_of_ne
            (fun h : ZetaPacketLabel.prime ℓ.1 ℓ.2 = ZetaPacketLabel.correction =>
              ZetaPacketLabel.noConfusion h))

/-- The canonical probe-dependent prime packet has zero correction coordinate. -/
theorem canonicalZetaPrimePacketAsEnsemble_correction_apply
    (f : ZetaAdmissibleFunction) :
    canonicalZetaPrimePacketAsEnsemble f ZetaPacketLabel.correction = 0 := by
  exact
    zetaPrimePacketAsEnsemble_correction_apply_at_bound
      f (canonicalZetaPaleyWienerSupportRadius f)

/-- An archimedean packet has zero correction coordinate. -/
theorem zetaArchimedeanPacketAsEnsemble_correction_apply
    (f : ZetaAdmissibleFunction) :
    zetaArchimedeanPacketAsEnsemble f ZetaPacketLabel.correction = 0 := by
  unfold zetaArchimedeanPacketAsEnsemble ZetaPacketEnsemble.single
  exact
    Finsupp.single_eq_of_ne
      (fun h : ZetaPacketLabel.archimedean = ZetaPacketLabel.correction =>
        ZetaPacketLabel.noConfusion h)

/-- The correction packet has the normalized coordinate in the correction slot. -/
theorem zetaCorrectionPacketAsEnsemble_correction_apply
    (f : ZetaAdmissibleFunction) :
    zetaCorrectionPacketAsEnsemble f ZetaPacketLabel.correction =
      zetaCompletionCorrectionPacketCoordinate := by
  unfold zetaCorrectionPacketAsEnsemble ZetaPacketEnsemble.single
  exact Finsupp.single_eq_same

/-- The completed zeta boundary defect decomposes into prime, archimedean, and correction parts. -/
theorem zetaCompletedBoundaryDefect_decomposition (f : ZetaAdmissibleFunction) :
    zetaCompletedBoundaryDefect f =
      zetaCompletedBoundaryDefectPrime f +
        zetaCompletedBoundaryDefectArchimedean f +
        zetaCompletedBoundaryDefectCorrection f := by
  rfl

/-- The explicit prime defect component is the reconstructed prime packet at the centered bound. -/
theorem zetaCompletedBoundaryDefectPrime_eq_packetPrime
    (f : ZetaAdmissibleFunction) :
    zetaCompletedBoundaryDefectPrime f = canonicalZetaPrimePacketAsEnsemble f := by
  rfl

/-- The explicit archimedean defect component is the reconstructed archimedean packet. -/
theorem zetaCompletedBoundaryDefectArchimedean_eq_packetArchimedean
    (f : ZetaAdmissibleFunction) :
    zetaCompletedBoundaryDefectArchimedean f =
      zetaArchimedeanPacketAsEnsemble f := by
  rfl

/-- The explicit correction defect component is the reconstructed centered correction packet. -/
theorem zetaCompletedBoundaryDefectCorrection_eq_packetCorrection
    (f : ZetaAdmissibleFunction) :
    zetaCompletedBoundaryDefectCorrection f =
      zetaCorrectionPacketAsEnsemble f := by
  rfl

/-- The explicit completed boundary defect is the reconstructed packet at the centered bound. -/
theorem zetaCompletedBoundaryDefect_eq_packetAsEnsemble
    (f : ZetaAdmissibleFunction) :
    zetaCompletedBoundaryDefect f = canonicalZetaPacketAsEnsemble f := by
  have hprime := zetaCompletedBoundaryDefectPrime_eq_packetPrime f
  have harch := zetaCompletedBoundaryDefectArchimedean_eq_packetArchimedean f
  have hcorrection := zetaCompletedBoundaryDefectCorrection_eq_packetCorrection f
  calc
    zetaCompletedBoundaryDefect f =
        zetaCompletedBoundaryDefectPrime f +
          zetaCompletedBoundaryDefectArchimedean f +
          zetaCompletedBoundaryDefectCorrection f := by
      rfl
    _ =
        canonicalZetaPrimePacketAsEnsemble f +
          zetaArchimedeanPacketAsEnsemble f +
          zetaCorrectionPacketAsEnsemble f := by
      exact congrArg₂ (fun a b : ZetaPacketEnsemble => a + b)
        (congrArg₂ (fun a b : ZetaPacketEnsemble => a + b) hprime harch)
        hcorrection
    _ = canonicalZetaPacketAsEnsemble f := by
      rfl

/-- The completed boundary defect has the normalized correction coordinate in the
correction slot. -/
theorem zetaCompletedBoundaryDefect_correction_apply
    (f : ZetaAdmissibleFunction) :
    zetaCompletedBoundaryDefect f ZetaPacketLabel.correction =
      zetaCompletionCorrectionPacketCoordinate := by
  calc
    zetaCompletedBoundaryDefect f ZetaPacketLabel.correction =
        zetaCompletedBoundaryDefectPrime f ZetaPacketLabel.correction +
            zetaCompletedBoundaryDefectArchimedean f ZetaPacketLabel.correction +
          zetaCompletedBoundaryDefectCorrection f ZetaPacketLabel.correction := by
      rfl
    _ =
        canonicalZetaPrimePacketAsEnsemble f ZetaPacketLabel.correction +
            zetaArchimedeanPacketAsEnsemble f ZetaPacketLabel.correction +
          zetaCorrectionPacketAsEnsemble f ZetaPacketLabel.correction := by
      rfl
    _ = 0 + 0 + zetaCompletionCorrectionPacketCoordinate := by
      exact congrArg₂ (fun a b : ℝ => a + b)
        (congrArg₂ (fun a b : ℝ => a + b)
          (canonicalZetaPrimePacketAsEnsemble_correction_apply f)
          (zetaArchimedeanPacketAsEnsemble_correction_apply f))
        (zetaCorrectionPacketAsEnsemble_correction_apply f)
    _ = zetaCompletionCorrectionPacketCoordinate := by
      exact
        Eq.trans
          (congrArg
            (fun x : ℝ => x + zetaCompletionCorrectionPacketCoordinate)
            (zero_add (0 : ℝ)))
          (zero_add zetaCompletionCorrectionPacketCoordinate)

/-- The correction slot belongs to the support of the completed boundary defect. -/
theorem zetaCompletedBoundaryDefect_correction_mem_support
    (f : ZetaAdmissibleFunction) :
    ZetaPacketLabel.correction ∈ (zetaCompletedBoundaryDefect f).support := by
  have hvalue :
      zetaCompletedBoundaryDefect f ZetaPacketLabel.correction =
        zetaCompletionCorrectionPacketCoordinate :=
    zetaCompletedBoundaryDefect_correction_apply f
  have hnonzero : zetaCompletionCorrectionPacketCoordinate ≠ 0 :=
    zetaCompletionCorrectionPacketCoordinate_ne_zero
  have hsupport : zetaCompletedBoundaryDefect f ZetaPacketLabel.correction ≠ 0 := by
    exact hvalue.trans_ne hnonzero
  exact Finsupp.mem_support_iff.mpr hsupport

/-- The correction part vanishes away from the correction label. -/
theorem zetaPacketEnsemble_correctionPart_sq_eq_zero_of_ne_correction
    (x : ZetaPacketEnsemble) (ℓ : ZetaPacketLabel)
    (hne : ℓ ≠ ZetaPacketLabel.correction) :
    ZetaPacketEnsemble.correctionPart x ℓ *
        ZetaPacketEnsemble.correctionPart x ℓ =
      0 :=
  match ℓ with
  | ZetaPacketLabel.prime m n =>
      let hzero :
          ZetaPacketEnsemble.correctionPart x (ZetaPacketLabel.prime m n) = 0 :=
        ZetaPacketEnsemble.correctionPart_prime x m n
      ZetaPacketEnsemble.sq_eq_zero_of_eq_zero hzero
  | ZetaPacketLabel.archimedean =>
      let hzero :
          ZetaPacketEnsemble.correctionPart x ZetaPacketLabel.archimedean = 0 :=
        ZetaPacketEnsemble.correctionPart_archimedean x
      ZetaPacketEnsemble.sq_eq_zero_of_eq_zero hzero
  | ZetaPacketLabel.correction =>
      False.elim (hne rfl)

/-- The correction label cannot be missing from the completed boundary-defect support. -/
theorem zetaCompletedBoundaryDefect_correction_not_not_mem_support
    (f : ZetaAdmissibleFunction)
    (hnotmem : ZetaPacketLabel.correction ∉ (zetaCompletedBoundaryDefect f).support) :
    False :=
  hnotmem (zetaCompletedBoundaryDefect_correction_mem_support f)

/-- The correction-part square sum of the completed boundary defect has only the
correction-label contribution. -/
theorem zetaCompletedBoundaryDefect_correctionPart_sq_sum_eq_single
    (f : ZetaAdmissibleFunction) :
    let x : ZetaPacketEnsemble := zetaCompletedBoundaryDefect f
    ∑ ℓ ∈ x.support,
        ZetaPacketEnsemble.correctionPart x ℓ *
          ZetaPacketEnsemble.correctionPart x ℓ =
      ZetaPacketEnsemble.correctionPart x ZetaPacketLabel.correction *
        ZetaPacketEnsemble.correctionPart x ZetaPacketLabel.correction := by
  intro x
  exact
    Finset.sum_eq_single ZetaPacketLabel.correction
      (fun ℓ _hℓ hne =>
        zetaPacketEnsemble_correctionPart_sq_eq_zero_of_ne_correction x ℓ hne)
      (fun hnotmem =>
        False.elim
          (zetaCompletedBoundaryDefect_correction_not_not_mem_support f hnotmem))

/-- The correction Gram of the completed boundary defect is the square of the
normalized correction coordinate. -/
theorem zetaCompletedBoundaryDefect_correctionPacketGram_eq_coordinate_sq
    (f : ZetaAdmissibleFunction) :
    ZetaPacketEnsemble.correctionPacketGram (zetaCompletedBoundaryDefect f) =
      zetaCompletionCorrectionPacketCoordinate *
        zetaCompletionCorrectionPacketCoordinate := by
  let x : ZetaPacketEnsemble := zetaCompletedBoundaryDefect f
  have hcorr :
      x ZetaPacketLabel.correction =
        zetaCompletionCorrectionPacketCoordinate :=
    zetaCompletedBoundaryDefect_correction_apply f
  have hcorrPart :
      ZetaPacketEnsemble.correctionPart x ZetaPacketLabel.correction =
        zetaCompletionCorrectionPacketCoordinate := by
    exact (ZetaPacketEnsemble.correctionPart_correction x).trans hcorr
  have hsum :
      ∑ ℓ ∈ x.support,
          ZetaPacketEnsemble.correctionPart x ℓ *
            ZetaPacketEnsemble.correctionPart x ℓ =
        ZetaPacketEnsemble.correctionPart x ZetaPacketLabel.correction *
          ZetaPacketEnsemble.correctionPart x ZetaPacketLabel.correction :=
    zetaCompletedBoundaryDefect_correctionPart_sq_sum_eq_single f
  calc
    ZetaPacketEnsemble.correctionPacketGram (zetaCompletedBoundaryDefect f) =
        ∑ ℓ ∈ x.support,
          ZetaPacketEnsemble.correctionPart x ℓ *
            ZetaPacketEnsemble.correctionPart x ℓ := by
      rfl
    _ =
        ZetaPacketEnsemble.correctionPart x ZetaPacketLabel.correction *
          ZetaPacketEnsemble.correctionPart x ZetaPacketLabel.correction := hsum
    _ =
        zetaCompletionCorrectionPacketCoordinate *
          zetaCompletionCorrectionPacketCoordinate := by
      exact congrArg (fun t : ℝ => t * t) hcorrPart

/-- The correction Gram of the real-shadow completed boundary defect is the centered
basepoint correction value. The owner correction contribution now depends on `Φ_f(0)`;
the variable autocorrelation normalization is handled in the Hermitian packet lane. -/
theorem zetaCompletedBoundaryDefect_correctionPacketGram_eq_centeredBasepointCorrection_re
    (f : ZetaAdmissibleFunction) :
    ZetaPacketEnsemble.correctionPacketGram (zetaCompletedBoundaryDefect f) =
      Complex.re (zetaCompletionCorrection 0) := by
  have hsquare :
      zetaCompletionCorrectionPacketCoordinate *
          zetaCompletionCorrectionPacketCoordinate =
        Complex.re (zetaCompletionCorrection 0) :=
    Boundary.LFunctions.zetaCompletionCorrectionPacketCoordinate_sq
  calc
    ZetaPacketEnsemble.correctionPacketGram (zetaCompletedBoundaryDefect f) =
        zetaCompletionCorrectionPacketCoordinate *
          zetaCompletionCorrectionPacketCoordinate :=
      zetaCompletedBoundaryDefect_correctionPacketGram_eq_coordinate_sq f
    _ = Complex.re (zetaCompletionCorrection 0) := hsquare

/-- The completed zeta boundary defect Gram norm square. -/
noncomputable def zetaCompletedBoundaryDefectGram (f : ZetaAdmissibleFunction) : ℝ :=
  ZetaPacketEnsemble.normSq (zetaCompletedBoundaryDefect f)

/-- The completed boundary defect Gram norm square is the packet norm square. -/
theorem zetaCompletedBoundaryDefectGram_eq_packetNormSq (f : ZetaAdmissibleFunction) :
    zetaCompletedBoundaryDefectGram f =
      ZetaPacketEnsemble.normSq (canonicalZetaPacketAsEnsemble f) := by
  exact congrArg ZetaPacketEnsemble.normSq (zetaCompletedBoundaryDefect_eq_packetAsEnsemble f)

/-- The completed boundary defect Gram norm is nonnegative. -/
theorem zetaCompletedBoundaryDefectGram_nonnegative (f : ZetaAdmissibleFunction) :
    0 ≤ zetaCompletedBoundaryDefectGram f := by
  have hpacket :
      0 ≤ ZetaPacketEnsemble.normSq (canonicalZetaPacketAsEnsemble f) :=
    canonicalZetaPacketAsEnsemble_normSq_nonnegative f
  have hgram :
      zetaCompletedBoundaryDefectGram f =
        ZetaPacketEnsemble.normSq (canonicalZetaPacketAsEnsemble f) :=
    zetaCompletedBoundaryDefectGram_eq_packetNormSq f
  exact Eq.subst (motive := fun x : ℝ => 0 ≤ x) hgram.symm hpacket

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
