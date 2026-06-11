import Boundary.LFunctions.ZetaPacketReconstruction
import Boundary.LFunctions.ZetaCompletionCorrection
import Boundary.LFunctions.ZetaExplicitFormulaAnalyticCore
import Boundary.LFunctions.WeilCriterion

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

/-- The prime component of the completed zeta boundary defect. -/
noncomputable def zetaCompletedBoundaryDefectPrime (f : ZetaAdmissibleFunction) :
    ZetaPacketEnsemble :=
  ∑ ℓ in zetaCompletedExplicitFormulaPrimeSupport,
    ZetaPacketEnsemble.single
      (ZetaPacketLabel.prime ℓ.1 ℓ.2)
      (Complex.re
        ((zetaCompletedExplicitFormulaPrimeWeight ℓ.1 ℓ.2 : ℂ) *
          ZetaTestFunction.primePacketTranslationDefect
            ℓ.1 ℓ.2 f.toZetaTestFunction' 0))

/-- The archimedean component of the completed zeta boundary defect. -/
noncomputable def zetaCompletedBoundaryDefectArchimedean (f : ZetaAdmissibleFunction) :
    ZetaPacketEnsemble :=
  ZetaPacketEnsemble.single .archimedean
    (Complex.re (zetaCompletedExplicitFormulaArchimedeanContribution f))

/-- The completion/correction component of the completed zeta boundary defect. -/
noncomputable def zetaCompletedBoundaryDefectCorrection (f : ZetaAdmissibleFunction) :
    ZetaPacketEnsemble :=
  ZetaPacketEnsemble.single .correction
    zetaCompletionCorrectionPacketCoordinate

/-- The completed zeta boundary defect attached to an admissible probe. -/
noncomputable def zetaCompletedBoundaryDefect (f : ZetaAdmissibleFunction) :
    ZetaPacketEnsemble :=
  zetaCompletedBoundaryDefectPrime f +
    zetaCompletedBoundaryDefectArchimedean f +
    zetaCompletedBoundaryDefectCorrection f

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
    zetaCompletedBoundaryDefectPrime f = zetaPrimePacketAsEnsemble f 0 := by
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
    zetaCompletedBoundaryDefect f = zetaPacketAsEnsemble f 0 := by
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
        zetaPrimePacketAsEnsemble f 0 +
          zetaArchimedeanPacketAsEnsemble f +
          zetaCorrectionPacketAsEnsemble f := by
      exact congrArg₂ (fun a b : ZetaPacketEnsemble => a + b)
        (congrArg₂ (fun a b : ZetaPacketEnsemble => a + b) hprime harch)
        hcorrection
    _ = zetaPacketAsEnsemble f 0 := by
      rfl

/-- The completed boundary defect has the normalized correction coordinate in the
correction slot. -/
theorem zetaCompletedBoundaryDefect_correction_apply
    (f : ZetaAdmissibleFunction) :
    zetaCompletedBoundaryDefect f ZetaPacketLabel.correction =
      zetaCompletionCorrectionPacketCoordinate := by
  simp [zetaCompletedBoundaryDefect, zetaCompletedBoundaryDefectPrime,
    zetaCompletedBoundaryDefectArchimedean, zetaCompletedBoundaryDefectCorrection,
    ZetaPacketEnsemble.single]

/-- The correction slot belongs to the support of the completed boundary defect. -/
theorem zetaCompletedBoundaryDefect_correction_mem_support
    (f : ZetaAdmissibleFunction) :
    ZetaPacketLabel.correction ∈ (zetaCompletedBoundaryDefect f).support := by
  have hvalue :
      zetaCompletedBoundaryDefect f ZetaPacketLabel.correction =
        zetaCompletionCorrectionPacketCoordinate :=
    zetaCompletedBoundaryDefect_correction_apply f
  have hnonzero : zetaCompletionCorrectionPacketCoordinate ≠ 0 := by
    norm_num [zetaCompletionCorrectionPacketCoordinate]
  simpa [Finsupp.mem_support_iff, hvalue] using hnonzero

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
          ZetaPacketEnsemble.correctionPart x ZetaPacketLabel.correction := by
    refine Finset.sum_eq_single ZetaPacketLabel.correction ?_ ?_
    · intro ℓ hℓ hne
      cases ℓ with
      | prime m n =>
          have hzero : ZetaPacketEnsemble.correctionPart x (ZetaPacketLabel.prime m n) = 0 :=
            ZetaPacketEnsemble.correctionPart_prime x m n
          exact ZetaPacketEnsemble.sq_eq_zero_of_eq_zero hzero
      | archimedean =>
          have hzero : ZetaPacketEnsemble.correctionPart x ZetaPacketLabel.archimedean = 0 :=
            ZetaPacketEnsemble.correctionPart_archimedean x
          exact ZetaPacketEnsemble.sq_eq_zero_of_eq_zero hzero
      | correction =>
          exact False.elim (hne rfl)
    · intro hnotmem
      have hmem : ZetaPacketLabel.correction ∈ x.support :=
        zetaCompletedBoundaryDefect_correction_mem_support f
      exact False.elim (hnotmem hmem)
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

/-- The correction Gram of the completed boundary defect is the real correction
contribution. -/
theorem zetaCompletedBoundaryDefect_correctionPacketGram_eq_correctionContribution_re
    (f : ZetaAdmissibleFunction) :
    ZetaPacketEnsemble.correctionPacketGram (zetaCompletedBoundaryDefect f) =
      Complex.re (zetaCompletedExplicitFormulaCorrectionContribution f) := by
  have hcorrection :
      zetaCompletedExplicitFormulaCorrectionContribution f =
        zetaCompletionCorrection 0 := by
    exact Boundary.LFunctions.zetaCompletionCorrection_zero.symm
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
    _ = Complex.re (zetaCompletedExplicitFormulaCorrectionContribution f) := by
      exact congrArg Complex.re hcorrection.symm

/-- The completed zeta boundary defect Gram norm square. -/
noncomputable def zetaCompletedBoundaryDefectGram (f : ZetaAdmissibleFunction) : ℝ :=
  ZetaPacketEnsemble.normSq (zetaCompletedBoundaryDefect f)

/-- The completed boundary defect Gram norm square is the packet norm square. -/
theorem zetaCompletedBoundaryDefectGram_eq_packetNormSq (f : ZetaAdmissibleFunction) :
    zetaCompletedBoundaryDefectGram f = zetaCompletedPacketNormSq f 0 := by
  exact congrArg ZetaPacketEnsemble.normSq (zetaCompletedBoundaryDefect_eq_packetAsEnsemble f)

/-- The completed boundary defect Gram norm is nonnegative. -/
theorem zetaCompletedBoundaryDefectGram_nonnegative (f : ZetaAdmissibleFunction) :
    0 ≤ zetaCompletedBoundaryDefectGram f := by
  have hpacket : 0 ≤ zetaCompletedPacketNormSq f 0 :=
    zetaCompletedPacketNormSq_nonnegative f 0
  have hgram :
      zetaCompletedBoundaryDefectGram f = zetaCompletedPacketNormSq f 0 :=
    zetaCompletedBoundaryDefectGram_eq_packetNormSq f
  exact Eq.subst (motive := fun x : ℝ => 0 ≤ x) hgram.symm hpacket

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
