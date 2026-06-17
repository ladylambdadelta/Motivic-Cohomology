import Boundary.LFunctionsRootedTreeCanonicalAll.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaCompletedHilbertSource.ZetaPacketComparison.ZetaCompletedBoundaryDefect.ZetaCompletedBoundaryDefect
import Boundary.LFunctionsRootedTreeCanonicalAll.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaCompletedHilbertSource.ZetaPacketComparison.ZetaCompletionCorrection.ZetaCompletionCorrection
import Boundary.LFunctionsRootedTreeCanonicalAll.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaAdmissibleSpectralInterpolation.ZetaAdmissiblePaleyWiener.ZetaExplicitFormulaAnalyticCore.ZetaExplicitFormulaAnalyticCore
import Boundary.LFunctionsRootedTreeCanonicalAll.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaCompletedHilbertSource.ZetaHermitianPacket.ZetaHermitianPacket

/-!
# Boundary zeta packet comparison

This file compares the packet reconstruction norm square with the completed
boundary-defect Gram form. It does not attempt the final Weil-form bridge; it
only isolates the owner-level packet identity already present in the
reconstruction layer.
-/

namespace Boundary
namespace LFunctions

noncomputable section

namespace ZetaAdmissibleFunction

/-- The completed explicit-formula prime support is the packet prime support at the centered bound. -/
theorem zetaCompletedExplicitFormulaPrimeSupport_eq_packetPrimeSupport_zero :
    zetaCompletedExplicitFormulaPrimeSupport = zetaPacketPrimeSupport 0 := by
  rfl

/-- The completed explicit-formula prime weight is the packet prime-label weight. -/
theorem zetaCompletedExplicitFormulaPrimeWeight_eq_packetWeight_prime
    (p n : ℕ) :
    zetaCompletedExplicitFormulaPrimeWeight p n =
      zetaPrimePacketWeight (ZetaPacketLabel.prime p n) := by
  rfl

/-- Real scalar action on a complex prime defect is the explicit complex product. -/
theorem zetaPrimePacketWeight_smul_defect_eq_mul
    (p n : ℕ) (f : ZetaAdmissibleFunction) :
    zetaPrimePacketWeight (ZetaPacketLabel.prime p n) •
        ZetaTestFunction.primePacketTranslationDefect p n f.toZetaTestFunction' 0 =
      (zetaCompletedExplicitFormulaPrimeWeight p n : ℂ) *
        ZetaTestFunction.primePacketTranslationDefect p n f.toZetaTestFunction' 0 := by
  rfl

/-- The prime packet is the finite packet of real parts of the explicit prime summands. -/
theorem zetaPrimePacketAsEnsemble_eq_explicitFormulaPrimePacket
    (f : ZetaAdmissibleFunction) :
    zetaPrimePacketAsEnsemble f 0 =
      ∑ ℓ in zetaCompletedExplicitFormulaPrimeSupport,
        ZetaPacketEnsemble.single
          (ZetaPacketLabel.prime ℓ.1 ℓ.2)
          (Complex.re
            ((zetaCompletedExplicitFormulaPrimeWeight ℓ.1 ℓ.2 : ℂ) *
              ZetaTestFunction.primePacketTranslationDefect
                ℓ.1 ℓ.2 f.toZetaTestFunction' 0)) := by
  rfl

/-- The archimedean packet is the singleton real part of the explicit archimedean contribution. -/
theorem zetaArchimedeanPacketAsEnsemble_eq_explicitFormulaArchimedeanPacket
    (f : ZetaAdmissibleFunction) :
    zetaArchimedeanPacketAsEnsemble f =
      ZetaPacketEnsemble.single .archimedean
        (Complex.re (zetaCompletedExplicitFormulaArchimedeanContribution f)) := by
  rfl

/-- The correction packet is the singleton normalized correction coordinate. -/
theorem zetaCorrectionPacketAsEnsemble_eq_normalizedCorrectionPacket
    (f : ZetaAdmissibleFunction) :
    zetaCorrectionPacketAsEnsemble f =
      ZetaPacketEnsemble.single .correction
        zetaCompletionCorrectionPacketCoordinate := by
  rfl

/-- The square of the correction packet coordinate is the real part of the explicit
centered correction contribution. -/
theorem zetaCorrectionPacketCoordinate_sq_eq_explicitFormulaCorrectionReal
    (f : ZetaAdmissibleFunction) :
    zetaCompletionCorrectionPacketCoordinate *
        zetaCompletionCorrectionPacketCoordinate =
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
    zetaCompletionCorrectionPacketCoordinate *
        zetaCompletionCorrectionPacketCoordinate =
        Complex.re (zetaCompletionCorrection 0) := hsquare
    _ = Complex.re (zetaCompletedExplicitFormulaCorrectionContribution f) := by
      exact congrArg Complex.re hcorrection.symm

/-- The reconstructed completed packet is exactly the packet built from the explicit-formula
prime and archimedean coordinates together with the normalized correction coordinate. -/
theorem zetaPacketAsEnsemble_eq_explicitFormulaPacket
    (f : ZetaAdmissibleFunction) :
    zetaPacketAsEnsemble f 0 =
      (∑ ℓ in zetaCompletedExplicitFormulaPrimeSupport,
        ZetaPacketEnsemble.single
          (ZetaPacketLabel.prime ℓ.1 ℓ.2)
          (Complex.re
            ((zetaCompletedExplicitFormulaPrimeWeight ℓ.1 ℓ.2 : ℂ) *
              ZetaTestFunction.primePacketTranslationDefect
                ℓ.1 ℓ.2 f.toZetaTestFunction' 0))) +
      ZetaPacketEnsemble.single .archimedean
        (Complex.re (zetaCompletedExplicitFormulaArchimedeanContribution f)) +
      ZetaPacketEnsemble.single .correction
        zetaCompletionCorrectionPacketCoordinate := by
  have hprime := zetaPrimePacketAsEnsemble_eq_explicitFormulaPrimePacket f
  have harch := zetaArchimedeanPacketAsEnsemble_eq_explicitFormulaArchimedeanPacket f
  have hcorrection := zetaCorrectionPacketAsEnsemble_eq_normalizedCorrectionPacket f
  calc
    zetaPacketAsEnsemble f 0 =
        zetaPrimePacketAsEnsemble f 0 +
          zetaArchimedeanPacketAsEnsemble f +
          zetaCorrectionPacketAsEnsemble f := by
      rfl
    _ =
        (∑ ℓ in zetaCompletedExplicitFormulaPrimeSupport,
          ZetaPacketEnsemble.single
            (ZetaPacketLabel.prime ℓ.1 ℓ.2)
            (Complex.re
              ((zetaCompletedExplicitFormulaPrimeWeight ℓ.1 ℓ.2 : ℂ) *
                ZetaTestFunction.primePacketTranslationDefect
                  ℓ.1 ℓ.2 f.toZetaTestFunction' 0))) +
        ZetaPacketEnsemble.single .archimedean
          (Complex.re (zetaCompletedExplicitFormulaArchimedeanContribution f)) +
        ZetaPacketEnsemble.single .correction
          zetaCompletionCorrectionPacketCoordinate := by
      exact congrArg₂ (fun a b : ZetaPacketEnsemble => a + b)
        (congrArg₂ (fun a b : ZetaPacketEnsemble => a + b) hprime harch)
        hcorrection

/-- The completed packet norm square is the completed boundary-defect Gram norm. -/
theorem zetaCompletedPacketNormSq_eq_boundaryDefectGram (f : ZetaAdmissibleFunction) :
    zetaCompletedPacketNormSq f 0 = zetaCompletedBoundaryDefectGram f := by
  exact (zetaCompletedBoundaryDefectGram_eq_packetNormSq f).symm

/-- The completed boundary-defect Gram norm is the completed packet norm square. -/
theorem zetaCompletedBoundaryDefectGram_eq_completedPacketNormSq
    (f : ZetaAdmissibleFunction) :
    zetaCompletedBoundaryDefectGram f = zetaCompletedPacketNormSq f 0 := by
  exact zetaCompletedBoundaryDefectGram_eq_packetNormSq f

/-- The completed packet norm square is nonnegative via the boundary-defect Gram. -/
theorem zetaCompletedPacketNormSq_nonnegative_of_boundaryDefect
    (f : ZetaAdmissibleFunction) :
    0 ≤ zetaCompletedPacketNormSq f 0 := by
  have hboundary : 0 ≤ zetaCompletedBoundaryDefectGram f :=
    zetaCompletedBoundaryDefectGram_nonnegative f
  have hgram :
      zetaCompletedBoundaryDefectGram f = zetaCompletedPacketNormSq f 0 :=
    zetaCompletedBoundaryDefectGram_eq_completedPacketNormSq f
  exact Eq.subst (motive := fun x : ℝ => 0 ≤ x) hgram hboundary

/-- The completed boundary-defect Gram agrees with the Hermitian packet norm-square. -/
theorem zetaCompletedBoundaryDefectGram_eq_realShadowComponents
    (f : ZetaAdmissibleFunction) :
    zetaCompletedBoundaryDefectGram f =
      ZetaPacketEnsemble.primePacketGram (zetaCompletedBoundaryDefect f) +
        ZetaPacketEnsemble.archimedeanPacketGram (zetaCompletedBoundaryDefect f) +
        ZetaPacketEnsemble.correctionPacketGram (zetaCompletedBoundaryDefect f) := by
  unfold zetaCompletedBoundaryDefectGram
  exact ZetaPacketEnsemble.zetaPacketNormSquare (zetaCompletedBoundaryDefect f)

/-- The real-shadow correction packet Gram agrees with the Hermitian correction packet Gram. -/
theorem zetaCompletedBoundaryDefect_correctionPacketGram_eq_HermitianCorrectionPacketGram
    (f : ZetaAdmissibleFunction) :
    ZetaPacketEnsemble.correctionPacketGram (zetaCompletedBoundaryDefect f) =
      ZetaHermitianPacketEnsemble.correctionPacketGram
        (zetaCompletedHermitianBoundaryDefect f) := by
  exact
    (zetaCompletedBoundaryDefect_correctionPacketGram_eq_coordinate_sq f).trans
      (zetaCompletedHermitianBoundaryDefect_correctionPacketGram_eq_coordinate_sq
        f).symm

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
