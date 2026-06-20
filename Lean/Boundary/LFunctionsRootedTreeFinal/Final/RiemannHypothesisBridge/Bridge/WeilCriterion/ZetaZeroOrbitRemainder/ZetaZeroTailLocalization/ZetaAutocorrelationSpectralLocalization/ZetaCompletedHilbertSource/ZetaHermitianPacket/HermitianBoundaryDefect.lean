import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaCompletedHilbertSource.ZetaHermitianPacket.CompletedPrimePowerPackets

namespace Boundary
namespace LFunctions

noncomputable section

open Filter
open scoped Topology

namespace ZetaAdmissibleFunction

/-- The archimedean Hermitian packet attached to the seed probe. -/
def zetaArchimedeanHermitianPacketAsEnsemble (f : ZetaAdmissibleFunction) :
    ZetaHermitianPacketEnsemble :=
  ZetaHermitianPacketEnsemble.single .archimedean
    (zetaCompletedExplicitFormulaArchimedeanSpectralAmplitude f)

/-- The normalized correction Hermitian packet. -/
def zetaCorrectionHermitianPacketAsEnsemble (_f : ZetaAdmissibleFunction) :
    ZetaHermitianPacketEnsemble :=
  ZetaHermitianPacketEnsemble.single .correction
    (zetaCompletedExplicitFormulaCorrectionSpectralAmplitude _f)

/-- The completed Hermitian boundary packet attached to a seed probe. -/
def zetaCompletedHermitianBoundaryDefect (f : ZetaAdmissibleFunction) :
    ZetaHermitianPacketEnsemble :=
  zetaPrimeHermitianPacketAsEnsemble f +
    zetaArchimedeanHermitianPacketAsEnsemble f +
    zetaCorrectionHermitianPacketAsEnsemble f

/-- The archimedean Hermitian packet has zero prime coordinates. -/
theorem zetaArchimedeanHermitianPacketAsEnsemble_prime_apply
    (p n : ℕ) (f : ZetaAdmissibleFunction) :
    zetaArchimedeanHermitianPacketAsEnsemble f
        (ZetaPacketLabel.prime p n) = 0 := by
  exact
    Finsupp.single_eq_of_ne
      (fun h : ZetaPacketLabel.archimedean = ZetaPacketLabel.prime p n =>
        ZetaPacketLabel.noConfusion h)

/-- The correction Hermitian packet has zero prime coordinates. -/
theorem zetaCorrectionHermitianPacketAsEnsemble_prime_apply
    (p n : ℕ) (f : ZetaAdmissibleFunction) :
    zetaCorrectionHermitianPacketAsEnsemble f
        (ZetaPacketLabel.prime p n) = 0 := by
  exact
    Finsupp.single_eq_of_ne
      (fun h : ZetaPacketLabel.correction = ZetaPacketLabel.prime p n =>
        ZetaPacketLabel.noConfusion h)

/-- The completed Hermitian boundary defect has the same prime coordinates as its
prime packet component. -/
theorem zetaCompletedHermitianBoundaryDefect_prime_apply
    (p n : ℕ) (f : ZetaAdmissibleFunction) :
    zetaCompletedHermitianBoundaryDefect f (ZetaPacketLabel.prime p n) =
      zetaPrimeHermitianPacketAsEnsemble f (ZetaPacketLabel.prime p n) := by
  have harch :
      zetaArchimedeanHermitianPacketAsEnsemble f
        (ZetaPacketLabel.prime p n) = 0 :=
    zetaArchimedeanHermitianPacketAsEnsemble_prime_apply p n f
  have hcorr :
      zetaCorrectionHermitianPacketAsEnsemble f
        (ZetaPacketLabel.prime p n) = 0 :=
    zetaCorrectionHermitianPacketAsEnsemble_prime_apply p n f
  calc
    (zetaPrimeHermitianPacketAsEnsemble f +
          zetaArchimedeanHermitianPacketAsEnsemble f +
          zetaCorrectionHermitianPacketAsEnsemble f)
        (ZetaPacketLabel.prime p n) =
        zetaPrimeHermitianPacketAsEnsemble f (ZetaPacketLabel.prime p n) +
          zetaArchimedeanHermitianPacketAsEnsemble f
            (ZetaPacketLabel.prime p n) +
          zetaCorrectionHermitianPacketAsEnsemble f
            (ZetaPacketLabel.prime p n) := by
      rfl
    _ =
        zetaPrimeHermitianPacketAsEnsemble f (ZetaPacketLabel.prime p n) +
          0 + 0 := by
      exact congrArg₂
        (fun a b : ℂ =>
          zetaPrimeHermitianPacketAsEnsemble f (ZetaPacketLabel.prime p n) +
            a + b)
        harch hcorr
    _ = zetaPrimeHermitianPacketAsEnsemble f (ZetaPacketLabel.prime p n) + 0 := by
      exact add_zero
        (zetaPrimeHermitianPacketAsEnsemble f (ZetaPacketLabel.prime p n) + 0)
    _ = zetaPrimeHermitianPacketAsEnsemble f (ZetaPacketLabel.prime p n) := by
      exact add_zero
        (zetaPrimeHermitianPacketAsEnsemble f (ZetaPacketLabel.prime p n))

/-- The completed Hermitian boundary defect and its prime component have the same prime
Hermitian Gram. -/
theorem zetaCompletedHermitianBoundaryDefect_primePacketGram_eq_primeComponent
    (f : ZetaAdmissibleFunction) :
    ZetaHermitianPacketEnsemble.primePacketGram
        (zetaCompletedHermitianBoundaryDefect f) =
      ZetaHermitianPacketEnsemble.primePacketGram
        (zetaPrimeHermitianPacketAsEnsemble f) := by
  exact
    ZetaHermitianPacketEnsemble.primePacketGram_eq_of_prime_coordinates
      (fun p n =>
        zetaCompletedHermitianBoundaryDefect_prime_apply p n f)

/-- The symmetrized real two-face completed boundary presentation. This is the unsigned
GNS matrix cross term.  The signed explicit-formula prime boundary channel is
`zetaCompletedPrimeTwoFaceGNSBoundaryCoefficient`, related to this prime coordinate by the
explicit boundary-sign theorem. -/
noncomputable def zetaCompletedGNSSymmetrizedBoundaryForm (f : ZetaAdmissibleFunction) : ℂ :=
  zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f +
    (ZetaHermitianPacketEnsemble.archimedeanPacketGram
      (zetaCompletedHermitianBoundaryDefect f) : ℂ) +
    (ZetaHermitianPacketEnsemble.correctionPacketGram
      (zetaCompletedHermitianBoundaryDefect f) : ℂ)

/-- The positive completed GNS boundary presentation form.

This is a complex spectral presentation: its prime channel is the defect-square kernel and
the symmetrized two-face prime channel is only the expansion cross term.  The ordered-heart
scalar is owned separately by `completedBoundaryGNSNormSq`. -/
noncomputable def zetaCompletedGNSPositiveBoundaryPresentationForm
    (f : ZetaAdmissibleFunction) : ℂ :=
  zetaCompletedPrimeDefectKernelPositiveForm f +
    (ZetaHermitianPacketEnsemble.archimedeanPacketGram
      (zetaCompletedHermitianBoundaryDefect f) : ℂ) +
    (ZetaHermitianPacketEnsemble.correctionPacketGram
      (zetaCompletedHermitianBoundaryDefect f) : ℂ)

/-- The real scalar attached to the positive completed GNS boundary presentation form. -/
noncomputable def zetaCompletedGNSPositiveBoundaryPresentationScalar
    (f : ZetaAdmissibleFunction) : ℝ :=
  Complex.re (zetaCompletedGNSPositiveBoundaryPresentationForm f)

/-- The finite display-level positive GNS boundary presentation form.

This is the packet/GNS positive square presentation over the explicit finite prime support.
It is separate from the completed prime-power presentation, whose prime channel is a
completed `tsum`. -/
noncomputable def zetaFiniteGNSPositiveBoundaryPresentationForm
    (f : ZetaAdmissibleFunction) : ℂ :=
  zetaPrimeDefectKernelPositiveForm f +
    (ZetaHermitianPacketEnsemble.archimedeanPacketGram
      (zetaCompletedHermitianBoundaryDefect f) : ℂ) +
    (ZetaHermitianPacketEnsemble.correctionPacketGram
      (zetaCompletedHermitianBoundaryDefect f) : ℂ)

/-- The real scalar attached to the finite positive GNS boundary presentation form. -/
noncomputable def zetaFiniteGNSPositiveBoundaryPresentationScalar
    (f : ZetaAdmissibleFunction) : ℝ :=
  Complex.re (zetaFiniteGNSPositiveBoundaryPresentationForm f)

/-- The completed GNS diagonal-debt boundary face associated with the prime defect-square
expansion. -/
noncomputable def zetaCompletedGNSDiagonalDebtBoundaryForm (f : ZetaAdmissibleFunction) : ℂ :=
  zetaCompletedPrimeDefectKernelDiagonalDebt f +
    (ZetaHermitianPacketEnsemble.archimedeanPacketGram
      (zetaCompletedHermitianBoundaryDefect f) : ℂ) +
    (ZetaHermitianPacketEnsemble.correctionPacketGram
      (zetaCompletedHermitianBoundaryDefect f) : ℂ)

/-- Compatibility alias for the symmetrized completed GNS boundary presentation.  This is the
completed cross-term surface, not the positive defect-kernel surface. -/
noncomputable def zetaCompletedGNSBoundaryForm (f : ZetaAdmissibleFunction) : ℂ :=
  zetaCompletedGNSSymmetrizedBoundaryForm f

/-- The finite display-level symmetrized boundary presentation reconstructed by the finite
packet surface.  This is intentionally separate from the completed prime-power GNS form:
finite packet reconstruction does not by itself identify the finite display channel with the
completed prime-power `tsum`. -/
noncomputable def zetaFiniteGNSSymmetrizedBoundaryForm (f : ZetaAdmissibleFunction) : ℂ :=
  zetaPrimeTwoFaceGNSMatrixCoefficient f +
    (ZetaHermitianPacketEnsemble.archimedeanPacketGram
      (zetaCompletedHermitianBoundaryDefect f) : ℂ) +
    (ZetaHermitianPacketEnsemble.correctionPacketGram
      (zetaCompletedHermitianBoundaryDefect f) : ℂ)

/-- The positive completed GNS boundary presentation form unfolds to the positive prime defect
kernel plus the archimedean and correction Gram channels. -/
theorem zetaCompletedGNSPositiveBoundaryPresentationForm_eq_primeDefect_add_archimedean_add_correction
    (f : ZetaAdmissibleFunction) :
    zetaCompletedGNSPositiveBoundaryPresentationForm f =
      zetaCompletedPrimeDefectKernelPositiveForm f +
        (ZetaHermitianPacketEnsemble.archimedeanPacketGram
          (zetaCompletedHermitianBoundaryDefect f) : ℂ) +
        (ZetaHermitianPacketEnsemble.correctionPacketGram
          (zetaCompletedHermitianBoundaryDefect f) : ℂ) := by
  rfl

/-- Scalar normal form for the positive completed GNS boundary presentation. -/
theorem zetaCompletedGNSPositiveBoundaryPresentationScalar_eq_primeDefect_add_archimedean_add_correction
    (f : ZetaAdmissibleFunction) :
    zetaCompletedGNSPositiveBoundaryPresentationScalar f =
      Complex.re (zetaCompletedPrimeDefectKernelPositiveForm f) +
        ZetaHermitianPacketEnsemble.archimedeanPacketGram
          (zetaCompletedHermitianBoundaryDefect f) +
        ZetaHermitianPacketEnsemble.correctionPacketGram
          (zetaCompletedHermitianBoundaryDefect f) := by
  let P : ℂ := zetaCompletedPrimeDefectKernelPositiveForm f
  let A : ℝ :=
    ZetaHermitianPacketEnsemble.archimedeanPacketGram
      (zetaCompletedHermitianBoundaryDefect f)
  let C : ℝ :=
    ZetaHermitianPacketEnsemble.correctionPacketGram
      (zetaCompletedHermitianBoundaryDefect f)
  calc
    Complex.re (P + (A : ℂ) + (C : ℂ)) =
        Complex.re (P + (A : ℂ)) + Complex.re (C : ℂ) := by
      exact Complex.add_re (P + (A : ℂ)) (C : ℂ)
    _ = (Complex.re P + Complex.re (A : ℂ)) + Complex.re (C : ℂ) := by
      exact congrArg
        (fun x : ℝ => x + Complex.re (C : ℂ))
        (Complex.add_re P (A : ℂ))
    _ = (Complex.re P + A) + C := by
      exact congrArg₂ HAdd.hAdd
        (congrArg₂ HAdd.hAdd rfl (Complex.ofReal_re A))
        (Complex.ofReal_re C)
    _ = Complex.re P + A + C := by
      rfl

/-- Scalar normal form for the finite positive GNS boundary presentation. -/
theorem zetaFiniteGNSPositiveBoundaryPresentationScalar_eq_primeDefect_add_archimedean_add_correction
    (f : ZetaAdmissibleFunction) :
    zetaFiniteGNSPositiveBoundaryPresentationScalar f =
      Complex.re (zetaPrimeDefectKernelPositiveForm f) +
        ZetaHermitianPacketEnsemble.archimedeanPacketGram
          (zetaCompletedHermitianBoundaryDefect f) +
        ZetaHermitianPacketEnsemble.correctionPacketGram
          (zetaCompletedHermitianBoundaryDefect f) := by
  let P : ℂ := zetaPrimeDefectKernelPositiveForm f
  let A : ℝ :=
    ZetaHermitianPacketEnsemble.archimedeanPacketGram
      (zetaCompletedHermitianBoundaryDefect f)
  let C : ℝ :=
    ZetaHermitianPacketEnsemble.correctionPacketGram
      (zetaCompletedHermitianBoundaryDefect f)
  calc
    Complex.re (P + (A : ℂ) + (C : ℂ)) =
        Complex.re (P + (A : ℂ)) + Complex.re (C : ℂ) := by
      exact Complex.add_re (P + (A : ℂ)) (C : ℂ)
    _ = (Complex.re P + Complex.re (A : ℂ)) + Complex.re (C : ℂ) := by
      exact congrArg
        (fun x : ℝ => x + Complex.re (C : ℂ))
        (Complex.add_re P (A : ℂ))
    _ = (Complex.re P + A) + C := by
      exact congrArg₂ HAdd.hAdd
        (congrArg₂ HAdd.hAdd rfl (Complex.ofReal_re A))
        (Complex.ofReal_re C)
    _ = Complex.re P + A + C := by
      rfl

/-- The symmetrized completed GNS boundary form unfolds to the unsigned two-face prime cross
term plus the archimedean and correction Gram channels. -/
theorem zetaCompletedGNSSymmetrizedBoundaryForm_eq_primeTwoFace_add_archimedean_add_correction
    (f : ZetaAdmissibleFunction) :
    zetaCompletedGNSSymmetrizedBoundaryForm f =
      zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f +
        (ZetaHermitianPacketEnsemble.archimedeanPacketGram
          (zetaCompletedHermitianBoundaryDefect f) : ℂ) +
        (ZetaHermitianPacketEnsemble.correctionPacketGram
          (zetaCompletedHermitianBoundaryDefect f) : ℂ) := by
  rfl

/-- The completed positive prime defect kernel plus its completed two-face cross term is the
completed prime diagonal debt. -/
theorem zetaCompletedPrimeDefectKernelPositiveForm_add_twoFace_eq_diagonalDebt
    (f : ZetaAdmissibleFunction) :
    zetaCompletedPrimeDefectKernelPositiveForm f +
        zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f =
      zetaCompletedPrimeDefectKernelDiagonalDebt f := by
  exact
    zetaCompletedPrimeDefectKernelPositiveWindow_expansion_passes_to_completedForms f

/-- Boundary-sign form of the completed prime defect expansion.

The explicit-formula boundary coefficient is the negative cross term, so the positive defect
kernel is obtained by adding diagonal debt to the boundary coefficient. -/
theorem zetaCompletedPrimeDefectKernelPositiveForm_eq_diagonalDebt_add_boundaryCoefficient
    (f : ZetaAdmissibleFunction) :
    zetaCompletedPrimeDefectKernelPositiveForm f =
      zetaCompletedPrimeDefectKernelDiagonalDebt f +
        zetaCompletedPrimeTwoFaceGNSBoundaryCoefficient f := by
  let P : ℂ := zetaCompletedPrimeDefectKernelPositiveForm f
  let T : ℂ := zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f
  let D : ℂ := zetaCompletedPrimeDefectKernelDiagonalDebt f
  have hcross : P + T = D :=
    zetaCompletedPrimeDefectKernelPositiveForm_add_twoFace_eq_diagonalDebt f
  have hboundary :
      zetaCompletedPrimeTwoFaceGNSBoundaryCoefficient f = -T := by
    exact zetaCompletedPrimeTwoFaceGNSBoundaryCoefficient_eq_neg_matrixCoefficient f
  calc
    P = P + T + -T := by
      exact (add_neg_cancel_right P T).symm
    _ = P + T + zetaCompletedPrimeTwoFaceGNSBoundaryCoefficient f := by
      exact congrArg (fun z : ℂ => P + T + z) hboundary.symm
    _ = D + zetaCompletedPrimeTwoFaceGNSBoundaryCoefficient f := by
      exact congrArg
        (fun z : ℂ => z + zetaCompletedPrimeTwoFaceGNSBoundaryCoefficient f)
        hcross

/-- Move the prime two-face channel across the two one-face square channels. -/
private theorem add_two_square_channels_right
    (P A C T : ℂ) :
    (P + A + C) + T = (P + T) + A + C :=
  calc
    (P + A + C) + T = (P + A) + (C + T) := by
      exact add_assoc (P + A) C T
    _ = (P + A) + (T + C) := by
      exact congrArg (fun z : ℂ => (P + A) + z) (add_comm C T)
    _ = P + (A + (T + C)) := by
      exact add_assoc P A (T + C)
    _ = P + (T + (A + C)) := by
      exact congrArg (fun z : ℂ => P + z) (add_left_comm A T C)
    _ = (P + T) + (A + C) := by
      exact (add_assoc P T (A + C)).symm
    _ = (P + T) + A + C := by
      exact (add_assoc (P + T) A C).symm

/-- Move the prime two-face channel through one copy of the square channels while retaining
the second square-channel copy. -/
private theorem add_two_square_channels_pair_right
    (P A C T : ℂ) :
    (P + A + C) + (T + A + C) = (P + T) + A + C + (A + C) :=
  calc
    (P + A + C) + (T + A + C) =
        (P + A + C) + (T + (A + C)) := by
      exact congrArg (fun z : ℂ => (P + A + C) + z) (add_assoc T A C)
    _ = ((P + A + C) + T) + (A + C) := by
      exact (add_assoc (P + A + C) T (A + C)).symm
    _ = ((P + T) + A + C) + (A + C) := by
      exact congrArg (fun z : ℂ => z + (A + C))
        (add_two_square_channels_right P A C T)
    _ = (P + T) + A + C + (A + C) := by
      rfl

/-- Boundary-level prime defect expansion: the positive GNS presentation form plus the prime
two-face cross term equals the diagonal-debt boundary form. -/
theorem zetaCompletedGNSPositiveBoundaryPresentationForm_add_primeTwoFace_eq_diagonalDebtBoundaryForm
    (f : ZetaAdmissibleFunction) :
    zetaCompletedGNSPositiveBoundaryPresentationForm f +
        zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f =
      zetaCompletedGNSDiagonalDebtBoundaryForm f := by
  let P : ℂ := zetaCompletedPrimeDefectKernelPositiveForm f
  let T : ℂ := zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f
  let D : ℂ := zetaCompletedPrimeDefectKernelDiagonalDebt f
  let A : ℂ :=
    (ZetaHermitianPacketEnsemble.archimedeanPacketGram
      (zetaCompletedHermitianBoundaryDefect f) : ℂ)
  let C : ℂ :=
    (ZetaHermitianPacketEnsemble.correctionPacketGram
      (zetaCompletedHermitianBoundaryDefect f) : ℂ)
  have hprime : P + T = D := by
    exact zetaCompletedPrimeDefectKernelPositiveForm_add_twoFace_eq_diagonalDebt f
  calc
    (P + A + C) + T = (P + T) + A + C := by
      exact add_two_square_channels_right P A C T
    _ = D + A + C := by
      exact congrArg (fun z : ℂ => z + A + C) hprime

/-- Full boundary-form expansion: adding the completed symmetrized boundary form to the positive
GNS presentation form replaces the prime cross term by diagonal debt and leaves a second copy
of the archimedean/correction square channels. -/
theorem zetaCompletedGNSPositiveBoundaryPresentationForm_add_symmetrized_eq_diagonalDebt_add_archCorrection
    (f : ZetaAdmissibleFunction) :
    zetaCompletedGNSPositiveBoundaryPresentationForm f +
        zetaCompletedGNSSymmetrizedBoundaryForm f =
      zetaCompletedGNSDiagonalDebtBoundaryForm f +
        ((ZetaHermitianPacketEnsemble.archimedeanPacketGram
            (zetaCompletedHermitianBoundaryDefect f) : ℂ) +
          (ZetaHermitianPacketEnsemble.correctionPacketGram
            (zetaCompletedHermitianBoundaryDefect f) : ℂ)) := by
  let P : ℂ := zetaCompletedPrimeDefectKernelPositiveForm f
  let T : ℂ := zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f
  let D : ℂ := zetaCompletedPrimeDefectKernelDiagonalDebt f
  let A : ℂ :=
    (ZetaHermitianPacketEnsemble.archimedeanPacketGram
      (zetaCompletedHermitianBoundaryDefect f) : ℂ)
  let C : ℂ :=
    (ZetaHermitianPacketEnsemble.correctionPacketGram
      (zetaCompletedHermitianBoundaryDefect f) : ℂ)
  have hprime : P + T = D := by
    exact zetaCompletedPrimeDefectKernelPositiveForm_add_twoFace_eq_diagonalDebt f
  calc
    (P + A + C) + (T + A + C) =
        (P + T) + A + C + (A + C) := by
      exact add_two_square_channels_pair_right P A C T
    _ = D + A + C + (A + C) := by
      exact congrArg (fun z : ℂ => z + A + C + (A + C)) hprime
    _ = (D + A + C) + (A + C) := by
      rfl

/-- The correction coordinate of the completed Hermitian boundary packet is the normalized
completion-correction coordinate. -/
theorem zetaCompletedHermitianBoundaryDefect_correction_apply
    (f : ZetaAdmissibleFunction) :
    zetaCompletedHermitianBoundaryDefect f ZetaPacketLabel.correction =
      (Boundary.LFunctions.zetaCompletionCorrectionPacketCoordinate : ℂ) := by
  have hprime :
      zetaPrimeHermitianPacketAsEnsemble f ZetaPacketLabel.correction = 0 :=
    zetaPrimeHermitianPacketAsEnsemble_correction_apply f
  have harch :
      zetaArchimedeanHermitianPacketAsEnsemble f ZetaPacketLabel.correction = 0 := by
    exact
      Finsupp.single_eq_of_ne
        (fun h : ZetaPacketLabel.archimedean = ZetaPacketLabel.correction =>
          ZetaPacketLabel.noConfusion h)
  have hcorr :
      zetaCorrectionHermitianPacketAsEnsemble f ZetaPacketLabel.correction =
        (Boundary.LFunctions.zetaCompletionCorrectionPacketCoordinate : ℂ) := by
    exact Finsupp.single_eq_same
  calc
    (zetaPrimeHermitianPacketAsEnsemble f +
          zetaArchimedeanHermitianPacketAsEnsemble f +
          zetaCorrectionHermitianPacketAsEnsemble f)
        ZetaPacketLabel.correction =
        zetaPrimeHermitianPacketAsEnsemble f ZetaPacketLabel.correction +
          zetaArchimedeanHermitianPacketAsEnsemble f ZetaPacketLabel.correction +
          zetaCorrectionHermitianPacketAsEnsemble f ZetaPacketLabel.correction := by
      rfl
    _ =
        0 + 0 +
          zetaCorrectionHermitianPacketAsEnsemble f ZetaPacketLabel.correction := by
      exact congrArg₂
        (fun a b : ℂ =>
          a + b +
            zetaCorrectionHermitianPacketAsEnsemble f ZetaPacketLabel.correction)
        hprime harch
    _ = 0 + 0 +
          (Boundary.LFunctions.zetaCompletionCorrectionPacketCoordinate : ℂ) := by
      exact congrArg (fun z : ℂ => 0 + 0 + z) hcorr
    _ = 0 +
          (Boundary.LFunctions.zetaCompletionCorrectionPacketCoordinate : ℂ) := by
      exact congrArg
        (fun z : ℂ =>
          z + (Boundary.LFunctions.zetaCompletionCorrectionPacketCoordinate : ℂ))
        (add_zero 0)
    _ = (Boundary.LFunctions.zetaCompletionCorrectionPacketCoordinate : ℂ) := by
      exact zero_add
        (Boundary.LFunctions.zetaCompletionCorrectionPacketCoordinate : ℂ)

/-- The correction Hermitian packet Gram is the square of the normalized correction coordinate. -/
theorem zetaCompletedHermitianBoundaryDefect_correctionPacketGram_eq_coordinate_sq
    (f : ZetaAdmissibleFunction) :
    ZetaHermitianPacketEnsemble.correctionPacketGram
        (zetaCompletedHermitianBoundaryDefect f) =
      Boundary.LFunctions.zetaCompletionCorrectionPacketCoordinate *
        Boundary.LFunctions.zetaCompletionCorrectionPacketCoordinate := by
  let x : ZetaHermitianPacketEnsemble := zetaCompletedHermitianBoundaryDefect f
  have hcorr :
      x ZetaPacketLabel.correction =
        (Boundary.LFunctions.zetaCompletionCorrectionPacketCoordinate : ℂ) :=
    zetaCompletedHermitianBoundaryDefect_correction_apply f
  have hcoord_nonzero :
      (Boundary.LFunctions.zetaCompletionCorrectionPacketCoordinate : ℂ) ≠ 0 := by
    intro hzero
    have hreal_zero :
        Boundary.LFunctions.zetaCompletionCorrectionPacketCoordinate = 0 :=
      Complex.ofReal_eq_zero.mp hzero
    have htwo_zero : (2 : ℝ) = 0 := by
      calc
        (2 : ℝ) = Boundary.LFunctions.zetaCompletionCorrectionPacketCoordinate := by
          rfl
        _ = 0 := hreal_zero
    exact (OfNat.ofNat_ne_zero 2) htwo_zero
  have hcorr_mem : ZetaPacketLabel.correction ∈ x.support := by
    exact Finsupp.mem_support_iff.mpr
      (fun hxzero => hcoord_nonzero (hcorr.symm.trans hxzero))
  have hsum :
      ∑ ℓ in x.support,
          (match ℓ with
          | .correction => ZetaHermitianPacketEnsemble.coordinateGram (x ℓ)
          | _ => 0) =
        ZetaHermitianPacketEnsemble.coordinateGram (x ZetaPacketLabel.correction) := by
    exact Finset.sum_eq_single ZetaPacketLabel.correction
      (fun ℓ hℓ hne => by
        cases ℓ with
        | prime p n => rfl
        | archimedean => rfl
        | correction => exact False.elim (hne rfl))
      (fun hnotmem => False.elim (hnotmem hcorr_mem))
  have hcoord :
      ZetaHermitianPacketEnsemble.coordinateGram (x ZetaPacketLabel.correction) =
        Boundary.LFunctions.zetaCompletionCorrectionPacketCoordinate *
          Boundary.LFunctions.zetaCompletionCorrectionPacketCoordinate := by
    calc
      ZetaHermitianPacketEnsemble.coordinateGram (x ZetaPacketLabel.correction) =
          ZetaHermitianPacketEnsemble.coordinateGram
            (Boundary.LFunctions.zetaCompletionCorrectionPacketCoordinate : ℂ) := by
        exact congrArg ZetaHermitianPacketEnsemble.coordinateGram hcorr
      _ =
          Boundary.LFunctions.zetaCompletionCorrectionPacketCoordinate *
            Boundary.LFunctions.zetaCompletionCorrectionPacketCoordinate := by
        exact Complex.normSq_ofReal
          Boundary.LFunctions.zetaCompletionCorrectionPacketCoordinate
  calc
    ZetaHermitianPacketEnsemble.correctionPacketGram
        (zetaCompletedHermitianBoundaryDefect f) =
        ∑ ℓ in x.support,
          match ℓ with
          | .correction => ZetaHermitianPacketEnsemble.coordinateGram (x ℓ)
          | _ => 0 := by
      rfl
    _ = ZetaHermitianPacketEnsemble.coordinateGram (x ZetaPacketLabel.correction) := hsum
    _ =
        Boundary.LFunctions.zetaCompletionCorrectionPacketCoordinate *
          Boundary.LFunctions.zetaCompletionCorrectionPacketCoordinate := hcoord

/-- The completed Hermitian packet norm square. -/
def zetaCompletedHermitianPacketNormSq (f : ZetaAdmissibleFunction) : ℝ :=
  ZetaHermitianPacketEnsemble.normSq (zetaCompletedHermitianBoundaryDefect f)

/-- The completed Hermitian packet norm square is nonnegative. -/
theorem zetaCompletedHermitianPacketNormSq_nonnegative
    (f : ZetaAdmissibleFunction) :
    0 ≤ zetaCompletedHermitianPacketNormSq f := by
  exact ZetaHermitianPacketEnsemble.normSq_nonnegative
    (zetaCompletedHermitianBoundaryDefect f)

/-- The finite prime Hermitian packet Gram is the displayed sum of defect-amplitude
coordinate Grams over the explicit prime support. -/
theorem zetaPrimeHermitianPacketAsEnsemble_primePacketGram_eq_finiteDefectAmplitudeSum
    (f : ZetaAdmissibleFunction) :
    ZetaHermitianPacketEnsemble.primePacketGram
        (zetaPrimeHermitianPacketAsEnsemble f) =
      ∑ ℓ in zetaCompletedExplicitFormulaPrimeSupport,
        ZetaHermitianPacketEnsemble.coordinateGram
          (zetaPrimeHermitianDefectAmplitude ℓ.1 ℓ.2 f) := by
  let x : ZetaHermitianPacketEnsemble := zetaPrimeHermitianPacketAsEnsemble f
  let label : ℕ × ℕ → ZetaPacketLabel :=
    fun ℓ => ZetaPacketLabel.prime ℓ.1 ℓ.2
  have hsupport :
      x.support ⊆ zetaCompletedExplicitFormulaPrimeSupport.image label :=
    zetaPrimeHermitianPacketAsEnsemble_support_subset_prime_image f
  have hgram :
      ZetaHermitianPacketEnsemble.primePacketGram x =
        ∑ τ in zetaCompletedExplicitFormulaPrimeSupport.image label,
          match τ with
          | .prime _ _ => ZetaHermitianPacketEnsemble.coordinateGram (x τ)
          | _ => 0 :=
    ZetaHermitianPacketEnsemble.primePacketGram_eq_sum_of_support_subset
      x
      (zetaCompletedExplicitFormulaPrimeSupport.image label)
      hsupport
  have hinj :
      ∀ a ∈ zetaCompletedExplicitFormulaPrimeSupport,
        ∀ b ∈ zetaCompletedExplicitFormulaPrimeSupport,
          label a = label b → a = b := by
    intro a _ b _ hab
    match a, b with
    | ⟨p, n⟩, ⟨q, r⟩ =>
        cases hab
        rfl
  have himage :
      (∑ τ in zetaCompletedExplicitFormulaPrimeSupport.image label,
          match τ with
          | .prime _ _ => ZetaHermitianPacketEnsemble.coordinateGram (x τ)
          | _ => 0) =
        ∑ ℓ in zetaCompletedExplicitFormulaPrimeSupport,
          ZetaHermitianPacketEnsemble.coordinateGram (x (label ℓ)) := by
    exact Finset.sum_image hinj
  have hcoords :
      (∑ ℓ in zetaCompletedExplicitFormulaPrimeSupport,
          ZetaHermitianPacketEnsemble.coordinateGram (x (label ℓ))) =
        ∑ ℓ in zetaCompletedExplicitFormulaPrimeSupport,
          ZetaHermitianPacketEnsemble.coordinateGram
            (zetaPrimeHermitianDefectAmplitude ℓ.1 ℓ.2 f) := by
    exact Finset.sum_congr rfl
      (fun ℓ hℓ => by
        exact congrArg ZetaHermitianPacketEnsemble.coordinateGram
          (zetaPrimeHermitianPacketAsEnsemble_prime_apply_of_mem f ℓ hℓ))
  exact hgram.trans (himage.trans hcoords)

/-- The prime Hermitian packet Gram is the real positive prime defect-kernel form. -/
theorem zetaCompletedHermitianBoundaryDefect_primePacketGram_eq_finiteDefectAmplitudeSum
    (f : ZetaAdmissibleFunction) :
    ZetaHermitianPacketEnsemble.primePacketGram
        (zetaCompletedHermitianBoundaryDefect f) =
      ∑ ℓ in zetaCompletedExplicitFormulaPrimeSupport,
        ZetaHermitianPacketEnsemble.coordinateGram
          (zetaPrimeHermitianDefectAmplitude ℓ.1 ℓ.2 f) := by
  exact
    (zetaCompletedHermitianBoundaryDefect_primePacketGram_eq_primeComponent
      f).trans
      (zetaPrimeHermitianPacketAsEnsemble_primePacketGram_eq_finiteDefectAmplitudeSum
        f)

/-- The finite positive prime defect form has real part equal to the finite defect-amplitude
Gram sum. -/
theorem zetaPrimeDefectKernelPositiveForm_re_eq_finiteDefectAmplitudeSum
    (f : ZetaAdmissibleFunction) :
    Complex.re (zetaPrimeDefectKernelPositiveForm f) =
      ∑ ℓ in zetaCompletedExplicitFormulaPrimeSupport,
        ZetaHermitianPacketEnsemble.coordinateGram
          (zetaPrimeHermitianDefectAmplitude ℓ.1 ℓ.2 f) := by
  calc
    Complex.re
        (∑ ℓ in zetaCompletedExplicitFormulaPrimeSupport,
          zetaPrimeDefectKernelPositiveCoordinate ℓ.1 ℓ.2 f) =
        ∑ ℓ in zetaCompletedExplicitFormulaPrimeSupport,
          Complex.re (zetaPrimeDefectKernelPositiveCoordinate ℓ.1 ℓ.2 f) := by
      exact Complex.re_sum
        zetaCompletedExplicitFormulaPrimeSupport
        (fun ℓ : ℕ × ℕ =>
          zetaPrimeDefectKernelPositiveCoordinate ℓ.1 ℓ.2 f)
    _ =
        ∑ ℓ in zetaCompletedExplicitFormulaPrimeSupport,
          ZetaHermitianPacketEnsemble.coordinateGram
            (zetaPrimeHermitianDefectAmplitude ℓ.1 ℓ.2 f) := by
      exact Finset.sum_congr rfl
        (fun ℓ _ =>
          zetaPrimeDefectKernelPositiveCoordinate_re_eq_defectAmplitude_normSq
            ℓ.1 ℓ.2 f)

/-- The prime Hermitian packet Gram is the real positive prime defect-kernel form. -/
theorem zetaCompletedHermitianBoundaryDefect_primePacketGram_eq_finitePrimeDefectKernelPositiveForm_re
    (f : ZetaAdmissibleFunction) :
    ZetaHermitianPacketEnsemble.primePacketGram
        (zetaCompletedHermitianBoundaryDefect f) =
      Complex.re (zetaPrimeDefectKernelPositiveForm f) := by
  exact
    (zetaCompletedHermitianBoundaryDefect_primePacketGram_eq_finiteDefectAmplitudeSum
      f).trans
      (zetaPrimeDefectKernelPositiveForm_re_eq_finiteDefectAmplitudeSum f).symm

/-- The Hermitian completed boundary-defect norm square is the finite positive GNS
presentation scalar. -/
theorem zetaCompletedHermitianBoundaryDefect_normSq_eq_finiteGNSPositiveBoundaryPresentationScalar
    (f : ZetaAdmissibleFunction) :
    ZetaHermitianPacketEnsemble.normSq (zetaCompletedHermitianBoundaryDefect f) =
      zetaFiniteGNSPositiveBoundaryPresentationScalar f := by
  let H : ZetaHermitianPacketEnsemble := zetaCompletedHermitianBoundaryDefect f
  let P : ℝ := Complex.re (zetaPrimeDefectKernelPositiveForm f)
  let A : ℝ := ZetaHermitianPacketEnsemble.archimedeanPacketGram H
  let C : ℝ := ZetaHermitianPacketEnsemble.correctionPacketGram H
  have hsplit :
      ZetaHermitianPacketEnsemble.normSq H =
        ZetaHermitianPacketEnsemble.primePacketGram H +
          ZetaHermitianPacketEnsemble.archimedeanPacketGram H +
          ZetaHermitianPacketEnsemble.correctionPacketGram H :=
    ZetaHermitianPacketEnsemble.normSq_eq_prime_add_archimedean_add_correction H
  have hprime :
      ZetaHermitianPacketEnsemble.primePacketGram H = P :=
    zetaCompletedHermitianBoundaryDefect_primePacketGram_eq_finitePrimeDefectKernelPositiveForm_re
      f
  have hfinite :
      zetaFiniteGNSPositiveBoundaryPresentationScalar f = P + A + C :=
    zetaFiniteGNSPositiveBoundaryPresentationScalar_eq_primeDefect_add_archimedean_add_correction
      f
  calc
    ZetaHermitianPacketEnsemble.normSq (zetaCompletedHermitianBoundaryDefect f) =
        ZetaHermitianPacketEnsemble.normSq H := by
      rfl
    _ =
        ZetaHermitianPacketEnsemble.primePacketGram H +
          ZetaHermitianPacketEnsemble.archimedeanPacketGram H +
          ZetaHermitianPacketEnsemble.correctionPacketGram H := by
      exact hsplit
    _ = P + A + C := by
      exact congrArg
        (fun x : ℝ => x + A + C)
        hprime
    _ = zetaFiniteGNSPositiveBoundaryPresentationScalar f := by
      exact hfinite.symm

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
